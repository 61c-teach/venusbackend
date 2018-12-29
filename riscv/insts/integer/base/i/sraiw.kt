package venusbackend.riscv.insts.integer.base.i

import venusbackend.numbers.toQuadWord
import venusbackend.riscv.insts.InstructionNotSupportedError
import venusbackend.riscv.insts.dsl.types.ShiftWImmediateInstruction

val sraiw = ShiftWImmediateInstruction(
        name = "sraiw",
        opcode = 0b0011011,
        funct3 = 0b101,
        funct7 = 0b0100000,
        eval16 = { a, b ->
            throw InstructionNotSupportedError("sraiw is not supported on 16 bit systems!")
        },
        eval32 = { a, b ->
            throw InstructionNotSupportedError("sraiw is not supported on 32 bit systems!")
        },
        eval64 = { a, b ->
            if (b == 0L) a.toInt().toLong() else (a.toInt() shr b.toInt()).toLong()
        },
        eval128 = { a, b ->
            if (b == 0.toQuadWord()) a.toInt().toQuadWord() else (a.toInt() shr b.toInt()).toQuadWord()
        }
)