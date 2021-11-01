package essent

import firrtl.ir.Circuit
import java.io.Writer

class JavaEmitter(initialOpt: OptFlags, writer: Writer) {
  val tabs = "  "

  def writeLines(indentLevel: Int, lines: String): Unit = writeLines(indentLevel, Seq(lines))

  def writeLines(indentLevel: Int, lines: Seq[String]): Unit = {
    lines.foreach { s => writer.write(tabs*indentLevel + s + "\n") }
  }

  def execute(circuit: Circuit): Unit = {
    writeLines(0, s"class ${circuit.main} {")
    writeLines(0, "}")
  }
}