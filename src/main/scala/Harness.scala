package essent

import firrtl._
import firrtl.ir._

import java.io.Writer

object HarnessGenerator {
  def harnessConnections(m: Module) = {
    // Attempts to reproduce the port ordering from chisel3 -> firrtl -> verilator
    // Reverses order of signals, but if signals are from same vec (share prefix
    // and have numeric suffix), reverses them (so vec signals are not reversed).
    def reorderPorts(signalNames: Seq[String]) = {
      def signalsFromSameVec(sigA: String, sigB: String) = {
        (sigA.count(_ == '_') > 1) && (sigB.count(_ == '_') > 1) &&
          (sigA.slice(0, sigA.lastIndexOf('_')) == sigB.slice(0, sigB.lastIndexOf('_'))) &&
          (sigA.drop(sigA.lastIndexOf('_')+1) forall Character.isDigit)
      }
      if (signalNames.isEmpty) signalNames
      else {
        val first = List(signalNames.head)
        val rest = signalNames.tail
        val contiguousPrefixes = rest.foldLeft(List[List[String]](first)) {
          (x,y) =>
            if (signalsFromSameVec(x.last.last, y)) x.init :+ (x.last ++ List(y))
            else x :+ List(y)
        }
        (contiguousPrefixes flatMap { _.reverse }).reverse
      }
    }
    def connectSignal(signalDirection: String)(signalName: String) = {
      s"comm->add_${signalDirection}signal(${signalName});"
    }
    val signalNames = scala.collection.mutable.ArrayBuffer.empty[String]
    val inputNames = scala.collection.mutable.ArrayBuffer.empty[String]
    val outputNames = scala.collection.mutable.ArrayBuffer.empty[String]
    val origOrderInputNames = scala.collection.mutable.ArrayBuffer.empty[String]
    m.ports foreach { p => {
      val sigName = s"&${p.name}"
      if (p.name == "clock" || p.name == "reset") {
        origOrderInputNames += sigName
        if (p.name == "reset")
          signalNames += sigName
      } else {
        p.direction match {
          case Input => inputNames += sigName
          case Output => outputNames += sigName
        }
      }
    }}
    val modName = m.name
    // val registerNames = registers map {r: DefRegister => r.name}
    val internalNames = Seq("reset") //++ registerNames
    val mapConnects = (internalNames.zipWithIndex) map {
      case (label: String, index: Int) => s"""comm->map_signal("$modName.$label", $index);"""
    }
    (origOrderInputNames ++ reorderPorts(inputNames) map connectSignal("in_")) ++
    (reorderPorts(outputNames) map connectSignal("out_")) ++
    (reorderPorts(signalNames) map connectSignal("")) ++ mapConnects
  }

  def topFile(circuitName: String, writer: Writer , vcdHeader: String) = {
    val baseStr = s"""|#include <iostream>
                      |
                      |#include "comm_wrapper.h"
                      |#include "$circuitName.h"
                      |
                      |int main() {
                      |  $circuitName dut;
                      |  CommWrapper<$circuitName> comm(dut);
                      |  comm.init_channels();
                      |  comm.init_sim_data();
                      |  dut.connect_harness(&comm); 
                      $vcdHeader
                      |  while (!comm.done()) {
                      |    comm.tick();
                      |  }
                      |  return 0;
                      |}
                      |""".stripMargin
    writer write baseStr
  }
}
