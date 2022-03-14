package venusbackend.simulator

/* ktlint-disable no-wildcard-imports */

import venus.Renderer
import venus.vfs.VirtualFileSystem
import venusbackend.*
import venusbackend.linker.LinkedProgram
import venusbackend.riscv.*
import venusbackend.riscv.insts.dsl.types.Instruction
import venusbackend.riscv.insts.floating.Decimal
import venusbackend.riscv.insts.integer.base.i.ecall.Alloc
import venusbackend.riscv.insts.integer.base.i.ecall.MCAlloc
import venusbackend.simulator.diffs.*
import venusbackend.simulator.plugins.SimulatorPlugin
import kotlin.math.max

/* ktlint-enable no-wildcard-imports */

/** Right now, this is a loose wrapper around SimulatorState
    Eventually, it will support debugging. */
open class Simulator(
    open val linkedProgram: LinkedProgram,
    open val VFS: VirtualFileSystem = VirtualFileSystem("dummy"),
    open var settings: SimulatorSettings = SimulatorSettings(),
    open val state: SimulatorState = SimulatorState32(),
    open val simulatorID: Int = 0
) {

    private var cycles = 0
    val history = History(settings.max_histroy)
    val preInstruction = ArrayList<Diff>()
    val postInstruction = ArrayList<Diff>()
//    private val breakpoints: Array<Boolean>
    private val breakpoints = HashSet<Int>()
    private val watchpoints = HashSet<WatchPoint>()
    var args = ArrayList<String>()
    var ebreak = false
    var atWatchPoint: HashSet<WatchPoint> = HashSet()
    var stdout = ""
    var filesHandler = FilesHandler(this)
    val instOrderMapping = HashMap<Int, Int>()
    val invInstOrderMapping = HashMap<Int, Int>()
    var exitcode: Int? = null

    val alloc: Alloc = if (settings.memcheck) {
        MCAlloc(this)
    } else {
        Alloc(this)
    }

    val plugins = LinkedHashMap<String, SimulatorPlugin>()

    init {
        (state).getReg(1)
        var i = 0
        for (inst in linkedProgram.prog.insts) {
            instOrderMapping[i] = state.getMaxPC().toInt()
            invInstOrderMapping[state.getMaxPC().toInt()] = i
            i++
            var mcode = inst[InstructionField.ENTIRE]
            for (j in 0 until inst.length) {
                state.mem.storeByte(state.getMaxPC(), mcode and 0xFF)
                mcode = mcode shr 8
                state.incMaxPC(1)
            }
        }

        var dataOffset = MemorySegments.STATIC_BEGIN
        for (datum in linkedProgram.prog.dataSegment) {
            state.mem.storeByte(dataOffset, datum.toInt())
            dataOffset++
        }

        state.setHeapEnd(max(state.getHeapEnd().toInt(), dataOffset))

        setPC(linkedProgram.startPC ?: MemorySegments.TEXT_BEGIN)
        if (settings.setRegesOnInit) {
            state.setReg(Registers.sp, MemorySegments.STACK_BEGIN)
//            state.setReg(Registers.fp, MemorySegments.STACK_BEGIN)
            state.setReg(Registers.gp, MemorySegments.STATIC_BEGIN)
            if (linkedProgram.prog.isGlobalLabel("main")) {
                state.setReg(Registers.ra, state.getMaxPC())
                settings.ecallOnlyExit = false // This is because this will not work with ecall exit only with this current hotfix
                try {
                    Renderer.updateRegister(Registers.ra, state.getMaxPC())
                } catch (e: Exception) {}
            }
        }

//        breakpoints = Array(linkedProgram.prog.insts.size, { false })

        if (this.settings.memcheckVerbose) {
            linkedProgram.prog.dataMemoryAllocs.sortBy { it.first }
            println("[memcheck] data allocs")
            for (alloc in linkedProgram.prog.dataMemoryAllocs) {
                println("[memcheck]     ptr=0x${alloc.first.toString(16).toUpperCase()} size=${alloc.second}")
            }
            println("[memcheck] end data allocs")
        }
    }

    fun registerPlugin(id: String, plugin: SimulatorPlugin): Boolean {
        if (id in this.plugins) {
            return false
        }
        plugin.init(this)
        this.plugins[id] = plugin
        return true
    }

    fun removePlugin(id: String): Boolean {
        if (id in this.plugins) {
            this.plugins.remove(id)
            return true
        }
        return false
    }

    fun finishPlugins() {
        plugins.values.forEach { it.finish(this) }
    }

    fun setHistoryLimit(limit: Int) {
        this.settings.max_histroy = limit
        this.history.limit = limit
    }

    fun isDone(): Boolean {
        return if (settings.ecallOnlyExit) {
            this.exitcode != null
        } else {
            getPC() >= state.getMaxPC()
        }
    }

    fun getCycles(): Int {
        return cycles
    }

    fun setCycles(c: Int) {
        cycles = c
    }

    fun getMaxPC(): Number {
        return state.getMaxPC()
    }

    fun incMaxPC(amount: Number) {
        state.incMaxPC(amount)
    }

    fun getInstAt(addr: Number): MachineCode {
        val instnum = invInstOrderMapping[addr]!!.toInt()
        return linkedProgram.prog.insts[instnum]
    }

    fun setMemory(mem: Memory) {
        state.mem = mem
    }

    fun run(plugins: List<SimulatorPlugin> = emptyList(), finishPluginsAfterRun: Boolean = true) {
        plugins.forEach { it.init(this) }
        while (!isDone()) {
            step(plugins)
        }
        if (finishPluginsAfterRun) {
            finishPlugins()
        }
        this.checkNumFreeBlocks()
    }

    fun runToBreakpoint(plugins: List<SimulatorPlugin> = emptyList()) {
        if (!isDone()) {
            // We need to step past a breakpoint.
            step(plugins)
        }
        while (!isDone() && !atBreakpoint()) {
            step(plugins)
        }
    }

    open fun step(plugins: List<SimulatorPlugin>): List<Diff> {
        val inst = getNextInstruction()
        val prevPC = getPC()
        this.atWatchPoint.clear()
        val diffs = step()
        plugins.forEach { it.onStep(this, inst, prevPC) }
        return diffs
    }

    open fun step(): List<Diff> {
        if (settings.maxSteps >= 0 && cycles >= settings.maxSteps) {
            throw ExceededAllowedCyclesError("Ran for more than the max allowed steps (${settings.maxSteps})!")
        }
        this.branched = false
        this.jumped = false
        this.ebreak = false
        this.atWatchPoint.clear()
        this.ecallMsg = ""
        cycles++
        preInstruction.clear()
        postInstruction.clear()
        val prevPC = getPC()
        val mcode: MachineCode = getNextInstruction()
        try {
            when (state.registerWidth) {
                16 -> { Instruction[mcode].impl16(mcode, this) }
                32 -> { Instruction[mcode].impl32(mcode, this) }
                64 -> { Instruction[mcode].impl64(mcode, this) }
                128 -> { Instruction[mcode].impl128(mcode, this) }
                else -> { throw SimulatorError("Unsupported register width!") }
            }
        } catch (e: SimulatorError) {
            if (e.infe == null) {
                throw e
            }
            Renderer.displayError("\n[ERROR]: Could not decode the instruction (0x" + mcode.toString(16) + ") at pc='" + toHex(getPC()) + "'!\n" +
                    "Please make sure that you are not jumping to the middle of an instruction!\n")
            throw e
        }
        history.add(preInstruction)
        this.stdout += this.ecallMsg
        if (isDone() && exitcode == null) {
            exitcode = state.getReg(Registers.a0).toInt()
        }
        this.plugins.values.forEach { it.onStep(this, mcode, prevPC) }
        return postInstruction.toList()
    }

    fun undo(): List<Diff> {
        exitcode = null
        if (!canUndo()) return emptyList() /* TODO: error here? */
        val diffs = history.pop()
        for (diff in diffs) {
            diff(state)
        }
        cycles--
        return diffs
    }

    fun removeAllArgsFromMem() {
        var sp = getReg(2)
        while (sp < MemorySegments.STACK_BEGIN && settings.setRegesOnInit) {
            this.state.mem.removeByte(sp)
            sp++
            setReg(Registers.sp, sp)
        }
    }

    fun removeAllArgs() {
        removeAllArgsFromMem()
        this.args.removeAll(this.args)
    }

    fun removeArg(index: Int) {
        if (index in 0 until this.args.size) {
            this.args.removeAt(index)
            this.removeAllArgsFromMem()
            addArgsToMem()
        }
    }

    fun addArg(arg: String) {
        args.add(arg)
        removeAllArgsFromMem()
        addArgsToMem()
    }

    fun addArg(newargs: List<String>) {
        args.addAll(newargs)
        removeAllArgsFromMem()
        addArgsToMem()
    }

    fun addArgsToMem() {
        val registerSize = state.registerWidth / 8
        val intSize = 4
        if (!settings.setRegesOnInit) {
            return
        }
        var spv = if (getReg(2) == MemorySegments.STACK_BEGIN) {
            getReg(2)
        } else {
            getReg(11)
        } - 1
        var argv = ArrayList<Number>()
        var tmpargs = arrayListOf(linkedProgram.prog.name)
        tmpargs.addAll(args)
        for (arg in tmpargs) {
            spv = getReg(Registers.sp) - 1
            /*Got to add the null terminator as well!*/
            storeByte(spv, 0)
            setRegNoUndo(Registers.sp, spv)
            for (c in arg.reversed()) {
                spv = getReg(Registers.sp) - 1
                storeByte(spv, c.toInt())
                setRegNoUndo(Registers.sp, spv)
            }
            argv.add(spv)
        }
        spv -= (spv % registerSize)
        /**
         * Next we need to create the argv array.
         */
        // First have to allocate a new space and load the null to the end of the array.
        spv -= intSize
        storeWord(spv, 0)
        // Next, we need to add the different arg strings to our argv array.
        for (arg in argv.reversed()) {
            spv -= intSize
            storeWord(spv, arg)
        }
        /**
         * We need to store a0 (x10) to the argc and a1 (x11) to argv.
         */
        setRegNoUndo(Registers.a0, tmpargs.size)
        setRegNoUndo(Registers.a1, spv)
        setRegNoUndo(Registers.sp, spv)
        try {
            Renderer.updateRegister(Registers.sp, getReg(Registers.sp))
            Renderer.updateRegister(Registers.a0, getReg(Registers.a0))
            Renderer.updateRegister(Registers.a1, getReg(Registers.a1))
            Renderer.updateMemory(Renderer.activeMemoryAddress)
        } catch (e: Throwable) {}
    }

    var ecallMsg = ""
    var branched = false
    var jumped = false
    fun reset(keep_args: Boolean = false) {
        while (this.canUndo()) {
            this.undo()
            cycles--
        }
        if (cycles > 0) {
            throw SimulatorError("Failed to reset as there is not enough history")
        }
        this.branched = false
        this.jumped = false
        this.ecallMsg = ""
        this.stdout = ""
        cycles = 0
        exitcode = null
        val args = ArrayList(this.args)
        removeAllArgs()
        if (keep_args) {
            addArg(args)
        }
        state.reset()
        this.plugins.values.forEach { it.reset(this) }
    }

    fun trace(): Tracer {
        return Tracer(this)
    }

    fun canUndo() = !history.isEmpty()

    fun getReg(id: Int) = state.getReg(id)

    fun setReg(id: Int, v: Number) {
        preInstruction.add(RegisterDiff(id, getReg(id)))
        state.setReg(id, v)
        postInstruction.add(RegisterDiff(id, getReg(id)))
    }

    fun setRegNoUndo(id: Int, v: Number) {
        state.setReg(id, v)
    }

    fun getFReg(id: Int) = state.getFReg(id)

    fun setFReg(id: Int, v: Decimal) {
        preInstruction.add(FRegisterDiff(id, state.getFReg(id)))
        state.setFReg(id, v)
        postInstruction.add(FRegisterDiff(id, state.getFReg(id)))
    }

    fun setFRegNoUndo(id: Int, v: Decimal) {
        state.setFReg(id, v)
    }

    fun toggleBreakpointAt(idx: Int): Boolean {
//        breakpoints[idx] = !breakpoints[idx]
//        return breakpoints[idx]
        if (breakpoints.contains(idx)) {
            breakpoints.remove(idx)
            return false
        } else {
            breakpoints.add(idx)
            return true
        }
    }

    /* TODO Make this more efficient while robust! */
    fun atBreakpoint(): Boolean {
        val location = (getPC() - MemorySegments.TEXT_BEGIN).toLong()
        val inst = invInstOrderMapping[location.toInt()]
        if (inst == null) {
//            Renderer.displayWarning("""Could not find an instruction mapped to the current address when checking for a breakpoint!""")
            return ebreak
        }
//        return ebreak || breakpoints[inst]
        val isEbreak = Instruction[getNextInstruction()].name == "ebreak"
        return (ebreak && !breakpoints.contains(location.toInt() - 4)) || (breakpoints.contains(location.toInt()) && !isEbreak) || (atWatchPoint.isNotEmpty())
//        return ebreak xor breakpoints.contains(location.toInt() - 4)
    }

    fun addWatchpoint(wp: WatchPoint): Boolean {
        return this.watchpoints.add(wp)
    }

    fun removeWatchpoint(wp: WatchPoint): Boolean {
        return this.watchpoints.remove(wp)
    }

    fun hasWatchpoint(wp: WatchPoint): Boolean {
        return this.watchpoints.contains(wp)
    }

    fun getTrigguredWatchpoints(): HashSet<WatchPoint>? {
        return atWatchPoint
    }

    fun handleWatchPoints(isStore: Boolean, addr: Number, value: Number) {
        this.watchpoints.forEach { wp ->
            if (wp.eval(isStore, addr, value)) {
                this.atWatchPoint.add(wp)
            }
        }
    }

    fun getPC() = state.getPC()

    fun setPC(newPC: Number) {
        preInstruction.add(PCDiff(getPC()))
        state.setPC(newPC)
        postInstruction.add(PCDiff(getPC()))
    }

    fun incrementPC(inc: Number) {
        preInstruction.add(PCDiff(getPC()))
        state.incPC(inc)
        postInstruction.add(PCDiff(getPC()))
    }

    fun isValidAccess(addr: Number, bytes: Int) {
        if (!this.settings.allowAccessBtnStackHeap) {
            if (this.settings.memcheck) {
                isValidAccessBetter(addr, bytes)
            } else {
                val upperAddr = addr + bytes
                val sp = state.getReg(Registers.sp)
                val heap = state.getHeapEnd()
                if ((addr > heap && addr < sp) ||
                        (upperAddr > heap && upperAddr < sp)) {
                    throw SimulatorError(
                            "Attempting to access uninitialized memory between the stack and heap. Attempting to access '$bytes' bytes at address '${Renderer.toHex(addr)}'.",
                            handled = true)
                }
            }
        }
    }

    fun isValidAccessBetter(addr: Number, bytes: Int) {
        val upperAddr = addr + bytes - 1
        val sp = state.getReg(Registers.sp)
        val pc = this.getPC()

        val instrIdx = this.invInstOrderMapping[this.getPC()]!!
        val dbg = this.linkedProgram.dbg[instrIdx]

        if (this.settings.memcheckVerbose) {
            Renderer.printConsole("[memcheck] access: addr=${Renderer.toHex(addr)} size=$bytes pc=${Renderer.toHex(pc)} file=${dbg.programName}:${dbg.dbg.lineNo} instr=${dbg.dbg.line.trim()}\n")
        }

        var referenceBlock: Pair<Int, Int>? = null
        var memType = ""
        var memLocationRel = "after"
        var diff = -1
        if ((addr > MemorySegments.HEAP_BEGIN && addr < sp) ||
            (upperAddr > MemorySegments.HEAP_BEGIN && upperAddr < sp)) {
            if (this.alloc !is MCAlloc) throw SimulatorError("Error: Simulator.alloc is not instance of MCAlloc. Please contact course staff. ")
            val results = this.isAddrInBlock(addr.toInt(), bytes, this.alloc.heapMemoryAllocs)
            if (!results.first) {
                // not in valid block, check if it was previously free'd
                val freeResults = this.isAddrInBlock(addr.toInt(), bytes, this.alloc.heapMemoryFrees)
                if (freeResults.first) {
                    referenceBlock = freeResults.second
                    memType = "free'd"
                    memLocationRel = "inside"
                    diff = max(0, referenceBlock.first - addr.toInt())
                } else {
                    referenceBlock = results.second
                    memType = "alloc'd"
                }
            }
        } else if ((addr > MemorySegments.STATIC_BEGIN && addr < MemorySegments.HEAP_BEGIN) ||
                (upperAddr > MemorySegments.STATIC_BEGIN && upperAddr < MemorySegments.HEAP_BEGIN)) {
            val results = this.isAddrInBlock(addr.toInt(), bytes, linkedProgram.prog.dataMemoryAllocs)
            if (!results.first) {
                referenceBlock = results.second
                memType = "in static"
            }
        }

        if (referenceBlock == null) return

        val regdump = this.getRegDump("\t")
        val debugStr = "\tProgram Counter: ${Renderer.toHex(pc)}\n" +
            "\tFile: ${dbg.programName}:${dbg.dbg.lineNo}\n" +
            "\tInstruction: ${dbg.dbg.line.trim()}\n" +
            regdump.trimEnd()
        if (referenceBlock.first == 0) {
            Renderer.displayError(
                "[memcheck] Invalid memory access of size $bytes. " +
                        "Address ${Renderer.toHex(addr)} is $memType.\n" +
                        debugStr + "\n")
        }
        if (diff == -1) diff = max(0, addr.toInt() - (referenceBlock.first + referenceBlock.second))
        Renderer.displayError(
            "[memcheck] Invalid memory access of size $bytes. " +
                    "Address ${Renderer.toHex(addr)} is $diff bytes $memLocationRel a block of size ${referenceBlock.second} $memType.\n" +
                    debugStr + "\n")
    }

    // returns Pair<isValid, closestBlock>,
    // closestBlock is either the previous block if not valid, or the block addr is in if valid
    private fun isAddrInBlock(addr: Int, size: Int, validBlocks: ArrayList<Pair<Int, Int>>): Pair<Boolean, Pair<Int, Int>> {
        val endAddr = addr + size - 1

        var idx = 0

        // Find which block addr is in, if any
        while (idx < validBlocks.size && validBlocks[idx].first + validBlocks[idx].second < addr) {
            idx += 1
        }
        if (idx >= validBlocks.size) {
            if (validBlocks.size == 0) return Pair(false, Pair(0, 0))
            return Pair(false, validBlocks[validBlocks.size - 1])
        }
        // idx is the first block that ends on or after addr
        if (addr < validBlocks[idx].first) {
            // if addr starts before the block, it is illegal access
            if (idx == 0) return Pair(false, Pair(0, 0))
            return Pair(false, validBlocks[idx - 1])
        } else if (endAddr >= validBlocks[idx].first + validBlocks[idx].second) {
            // endAddr is after block ends
            return Pair(false, validBlocks[idx])
        } else {
            return Pair(true, validBlocks[idx])
        }
    }

    private fun checkNumFreeBlocks() {
        if (this.settings.memcheck && this.alloc is MCAlloc) {
            val numBlocks = this.alloc.heapMemoryAllocs.size
            val numBytes = if (numBlocks == 0) {
                0
            } else {
                this.alloc.heapMemoryAllocs.map { it.second }.reduce { acc, int -> acc + int }
            }
            var errorMsg = "[memcheck] In use at exit: $numBytes bytes in $numBlocks blocks"
            if (this.settings.memcheckVerbose) {
                for (block in this.alloc.heapMemoryAllocs) {
                    errorMsg += "\n\t${block.second} bytes at ${Renderer.toHex(block.first)} is lost"
                }
            } else {
                errorMsg += "\n[memcheck] For detailed leak analysis, rerun with --memcheckVerbose"
            }
            if (this.settings.memcheckVerbose || numBlocks > 0) {
                Renderer.displayError(errorMsg + "\n")
            } else if (this.settings.memcheckVerbose) {
                Renderer.printConsole(errorMsg + "\n")
            }
        }
    }

    private fun getRegDump(prefix: String = ""): String {
        var regdump = "${prefix}Registers:                    " // save space for x0
        for (i in 1..31) {
            if (i % 4 == 0) regdump = regdump.trimEnd() + "\n$prefix          "
            val regnum = "x$i(${getRegNameFromIndex(i, true)})".padStart(8)
            regdump += "$regnum=${Renderer.toHex(this.getReg(i))} "
        }
        return regdump
    }

    fun loadByte(addr: Number, handleWatchpoint: Boolean = true): Int {
        val value = state.mem.loadByte(addr)
        if (handleWatchpoint) {
            handleWatchPoints(false, addr, value)
        }
        return value
    }
    fun loadBytewCache(addr: Number, isSyscall: Boolean = false): Int {
        if (this.settings.alignedAddress && addr % MemSize.BYTE.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not BYTE aligned!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.BYTE.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.BYTE)))
        state.cache.read(Address(addr, MemSize.BYTE))
        postInstruction.add(CacheDiff(Address(addr, MemSize.BYTE)))
        return this.loadByte(addr)
    }
    fun loadBytewCache(addr: Number): Int {
        return this.loadBytewCache(addr, false)
    }

    fun loadHalfWord(addr: Number, handleWatchpoint: Boolean = true): Int {
        val value = state.mem.loadHalfWord(addr)
        if (handleWatchpoint) {
            handleWatchPoints(false, addr, value)
        }
        return value
    }
    fun loadHalfWordwCache(addr: Number, isSyscall: Boolean = false): Int {
        if (this.settings.alignedAddress && addr % MemSize.HALF.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not HALF WORD aligned!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.HALF.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.HALF)))
        state.cache.read(Address(addr, MemSize.HALF))
        postInstruction.add(CacheDiff(Address(addr, MemSize.HALF)))
        return this.loadHalfWord(addr)
    }
    fun loadHalfWordwCache(addr: Number): Int {
        return this.loadHalfWordwCache(addr, false)
    }

    fun loadWord(addr: Number, handleWatchpoint: Boolean = true): Int {
        val value = state.mem.loadWord(addr)
        if (handleWatchpoint) {
            handleWatchPoints(false, addr, value)
        }
        return value
    }
    fun loadWordwCache(addr: Number, isSyscall: Boolean = false): Int {
        if (this.settings.alignedAddress && addr % MemSize.WORD.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not WORD aligned!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.WORD.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.WORD)))
        state.cache.read(Address(addr, MemSize.WORD))
        postInstruction.add(CacheDiff(Address(addr, MemSize.WORD)))
        return this.loadWord(addr)
    }
    fun loadWordwCache(addr: Number): Int {
        return this.loadWordwCache(addr, false)
    }

    fun loadLong(addr: Number, handleWatchpoint: Boolean = true): Long {
        val value = state.mem.loadLong(addr)
        if (handleWatchpoint) {
            handleWatchPoints(false, addr, value)
        }
        return value
    }
    fun loadLongwCache(addr: Number, isSyscall: Boolean = false): Long {
        if (this.settings.alignedAddress && addr % MemSize.LONG.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not LONG aligned!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.LONG.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.LONG)))
        state.cache.read(Address(addr, MemSize.LONG))
        postInstruction.add(CacheDiff(Address(addr, MemSize.LONG)))
        return this.loadLong(addr)
    }
    fun loadLongwCache(addr: Number): Long {
        return this.loadLongwCache(addr, false)
    }

    fun storeByte(addr: Number, value: Number) {
        preInstruction.add(MemoryDiff(addr, loadWord(addr, handleWatchpoint = false)))
        state.mem.storeByte(addr, value)
        handleWatchPoints(true, addr, value)
        postInstruction.add(MemoryDiff(addr, loadWord(addr, handleWatchpoint = false)))
        this.storeTextOverrideCheck(addr, value, MemSize.BYTE)
    }
    fun storeBytewCache(addr: Number, value: Number, isSyscall: Boolean = false) {
        if (this.settings.alignedAddress && addr % MemSize.BYTE.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not BYTE aligned!")
        }
        // FIXME change the cast to maxpc to something more generic or make the iterator be generic.
        if (!this.settings.mutableText && addr in (MemorySegments.TEXT_BEGIN + 1 - MemSize.BYTE.size)..state.getMaxPC().toInt()) {
            throw StoreError("You are attempting to edit the text of the program though the program is set to immutable at address " + Renderer.toHex(addr) + "!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.BYTE.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.BYTE)))
        state.cache.write(Address(addr, MemSize.BYTE))
        this.storeByte(addr, value)
        postInstruction.add(CacheDiff(Address(addr, MemSize.BYTE)))
    }
    fun storeBytewCache(addr: Number, value: Number) {
        this.storeBytewCache(addr, value, false)
    }

    fun storeHalfWord(addr: Number, value: Number) {
        preInstruction.add(MemoryDiff(addr, loadWord(addr, handleWatchpoint = false)))
        state.mem.storeHalfWord(addr, value)
        handleWatchPoints(true, addr, value)
        postInstruction.add(MemoryDiff(addr, loadWord(addr, handleWatchpoint = false)))
        this.storeTextOverrideCheck(addr, value, MemSize.HALF)
    }
    fun storeHalfWordwCache(addr: Number, value: Number, isSyscall: Boolean = false) {
        if (this.settings.alignedAddress && addr % MemSize.HALF.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not HALF WORD aligned!")
        }
        if (!this.settings.mutableText && addr in (MemorySegments.TEXT_BEGIN + 1 - MemSize.HALF.size)..state.getMaxPC().toInt()) {
            throw StoreError("You are attempting to edit the text of the program though the program is set to immutable at address " + Renderer.toHex(addr) + "!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.HALF.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.HALF)))
        state.cache.write(Address(addr, MemSize.HALF))
        this.storeHalfWord(addr, value)
        postInstruction.add(CacheDiff(Address(addr, MemSize.HALF)))
    }
    fun storeHalfWordwCache(addr: Number, value: Number) {
        this.storeHalfWordwCache(addr, value, false)
    }

    fun storeWord(addr: Number, value: Number) {
        preInstruction.add(MemoryDiff(addr, loadWord(addr, handleWatchpoint = false)))
        state.mem.storeWord(addr, value)
        handleWatchPoints(true, addr, value)
        postInstruction.add(MemoryDiff(addr, loadWord(addr, handleWatchpoint = false)))
        this.storeTextOverrideCheck(addr, value, MemSize.WORD)
    }
    fun storeWordwCache(addr: Number, value: Number, isSyscall: Boolean = false) {
        if (this.settings.alignedAddress && addr % MemSize.WORD.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not WORD aligned!")
        }
        if (!this.settings.mutableText && addr in (MemorySegments.TEXT_BEGIN + 1 - MemSize.WORD.size)..state.getMaxPC().toInt()) {
            throw StoreError("You are attempting to edit the text of the program though the program is set to immutable at address " + Renderer.toHex(addr) + "!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.WORD.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.WORD)))
        state.cache.write(Address(addr, MemSize.WORD))
        this.storeWord(addr, value)
        postInstruction.add(CacheDiff(Address(addr, MemSize.WORD)))
    }
    fun storeWordwCache(addr: Number, value: Number) {
        this.storeWordwCache(addr, value, false)
    }

    fun storeLong(addr: Number, value: Number) {
        preInstruction.add(MemoryDiff(addr, loadLong(addr, handleWatchpoint = false)))
        state.mem.storeLong(addr, value)
        handleWatchPoints(true, addr, value)
        postInstruction.add(MemoryDiff(addr, loadLong(addr, handleWatchpoint = false)))
        this.storeTextOverrideCheck(addr, value, MemSize.LONG)
    }
    fun storeLongwCache(addr: Number, value: Number, isSyscall: Boolean = false) {
        if (this.settings.alignedAddress && addr % MemSize.LONG.size != 0) {
            throw AlignmentError("Address: '" + Renderer.toHex(addr) + "' is not long aligned!")
        }
        if (!this.settings.mutableText && addr in (MemorySegments.TEXT_BEGIN + 1 - MemSize.WORD.size)..state.getMaxPC().toInt()) {
            throw StoreError("You are attempting to edit the text of the program though the program is set to immutable at address " + Renderer.toHex(addr) + "!")
        }
        if (!isSyscall) this.isValidAccess(addr, MemSize.LONG.size)
        preInstruction.add(CacheDiff(Address(addr, MemSize.LONG)))
        state.cache.write(Address(addr, MemSize.LONG))
        this.storeLong(addr, value)
        postInstruction.add(CacheDiff(Address(addr, MemSize.LONG)))
    }
    fun storeLongwCache(addr: Number, value: Number) {
        this.storeLongwCache(addr, value, false)
    }

    fun storeTextOverrideCheck(addr: Number, value: Number, size: MemSize) {
        /*Here, we will check if we are writing to memory*/
        if (addr in (MemorySegments.TEXT_BEGIN until state.getMaxPC().toInt()) || (addr + size.size - MemSize.BYTE.size) in (MemorySegments.TEXT_BEGIN until state.getMaxPC().toInt())) {
            try {
                val adjAddr = ((addr / MemSize.WORD.size) * MemSize.WORD.size)
                val lowerAddr = adjAddr - MemorySegments.TEXT_BEGIN
                var newInst = this.state.mem.loadWord(adjAddr)
                preInstruction.add(Renderer.updateProgramListing(lowerAddr, newInst))
                if ((lowerAddr + MemorySegments.TEXT_BEGIN) != addr && (lowerAddr + MemSize.WORD.size - MemSize.BYTE.size) < state.getMaxPC()) {
                    var newInst2 = this.state.mem.loadWord(adjAddr + MemSize.WORD.size)
                    preInstruction.add(Renderer.updateProgramListing((lowerAddr) + 4, newInst2))
                }
            } catch (e: Throwable) { /*This is to not error the tests.*/ }
        }
    }

    fun getHeapEnd() = state.getHeapEnd()

    fun addHeapSpace(bytes: Number) {
        if (willHeapOverrideStack(bytes)) {
            throw SimulatorError("The heap has grown into the stack.")
        }
        preInstruction.add(HeapSpaceDiff(state.getHeapEnd()))
        state.incHeapEnd(bytes)
        postInstruction.add(HeapSpaceDiff(state.getHeapEnd()))
    }

    fun willHeapOverrideStack(bytes: Number): Boolean {
        return (getHeapEnd() + bytes) >= getReg(Registers.sp)
    }

    private fun getInstructionLength(short0: Int): Int {
        if ((short0 and 0b11) != 0b11) {
            return 2
        } else if ((short0 and 0b11111) != 0b11111) {
            return 4
        } else if ((short0 and 0b111111) == 0b011111) {
            return 6
        } else if ((short0 and 0b1111111) == 0b111111) {
            return 8
        } else {
            throw SimulatorError("instruction lengths > 8 not supported")
        }
    }

    fun getNextInstruction(): MachineCode {
        val pc = getPC()
        var instruction: ULong = loadHalfWord(pc).toULong()
        val length = getInstructionLength(instruction.toInt())
        for (i in 1 until length / 2) {
            val short = loadHalfWord(pc + 2).toULong()
            instruction = (short shl 16 * i) or instruction
        }
        val intStruction = instruction.toInt()
        val mcode = MachineCode(intStruction)
        mcode.length = length
        return mcode
    }

    fun memcpy(destaddr: Int, srcaddr: Int, size: Int): Int {
        var dest = destaddr
        var src = srcaddr
        var s = size
        while (s > 0) {
            storeByte(dest, loadByte(src))
            dest++
            src++
            s--
        }
        return destaddr
    }

    fun memset(destaddr: Int, item: Int, size: Int): Int {
        var dest = destaddr
        var s = size
        while (s > 0) {
            storeByte(dest, item)
            dest++
            s--
        }
        return destaddr
    }

    fun coreDump(): HashMap<String, Any> {
        val d = HashMap<String, Any>()
        val integer = HashMap<Int, Number>()
        val floating = HashMap<Int, Decimal>()
        for (i in 1 until 32) {
            integer[i] = this.getReg(i)
            floating[i] = this.getFReg(i)
        }
        val registers = HashMap<String, Any>()
        registers["integer"] = integer
        registers["floating"] = floating
        d["registers"] = registers
        d["memory"] = this.state.mem.dump()
        return d
    }
}

// data class CoreDump(
//        var time: String,
//        var regisers: CoreDumpRegisters,
//        var memory: HashMap<Int, Int>
// )
//
// data class CoreDumpRegisters(
//        var integer: CoreDumpRegister,
//        var floating: CoreDumpRegister
// )
//
// data class CoreDumpRegister(
//        var id: String,
//        var value: String
// )