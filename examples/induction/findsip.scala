import at.logic.gapt.examples.UniformAssociativity3ExampleProof
import at.logic.gapt.expr.hol.{toNNF, simplify, lcomp}
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.grammars.{minimizeSipGrammar, SipGrammarMinimizationFormula, normalFormsSipGrammar, GrammarMinimizationFormula}
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkNew.LKToExpansionProof
import at.logic.gapt.provers.maxsat.QMaxSAT
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.utils.time

def removeEqAxioms( eseq: ExpansionSequent ) = {
  // removes all equality axioms that appear in examples/ProofSequences.scala
  val R = parseFormula( "(Forall x x = x" )
  val S = parseFormula( "(all x (all y (x = y -> y = x)))" )
  val T = parseFormula( "(all x (all y (all z (x = y & y = z) ->  x = z)))" )
  val Tprime = parseFormula( "(all x (all y (all z x = y ->  (y = z ->  x = z)))" )
  val CSuc = parseFormula( "(all x (all y x = y  -> s(x) = s(y)))" )
  val CPlus = parseFormula( "(all x (all y (all u (all v x = y -> (u = v ->  x + u = y + v )))))" )
  val CPlusL = parseFormula( "(all x (all y (all z y = z -> y + x = z + x )))" ) // congruence plus left
  val CgR = parseFormula( "(all x (all y (all z y = z ->  g(x,y) = g(x,z) )))" ) // congruence of g on the right
  val CMultR = parseFormula( "(all x (all y (all z x = y -> z * x = z * y )))" ) // congruence of mult right

  val eqaxioms = new HOLSequent( R::S::T::Tprime::CSuc::CPlus::CPlusL::CgR::CMultR::Nil, Nil )

  removeFromExpansionSequent( eseq, eqaxioms )
}

val N = 5
var instanceSequents = (1 until N) map { n =>
  val instanceProof = UniformAssociativity3ExampleProof(n)
//  val instanceProof = LinearEqExampleProof(n)
//  val instanceProof = FactorialFunctionEqualityExampleProof(n)
  n -> removeEqAxioms(LKToExpansionProof(instanceProof))
}

val endSequent = HOLSequent(
  instanceSequents.flatMap{ case (n,seq) => toShallow(seq).antecedent }.distinct,
  Seq(parseFormula("(x + x) + x = x + (x + x)"))
)
println(s"End-sequent of the sip: $endSequent")

val nLine = sys.props("line.separator")

val encoding = InstanceTermEncoding(endSequent)
var instanceLanguages = instanceSequents.map { case (n, seq) =>
  n -> encoding.encode(seq)
}
// patch up missing case for n=0
instanceLanguages = instanceLanguages ++
  Seq(0 -> Seq(encoding.encode(parseFormula("0+0=0") -> true)))
instanceLanguages foreach { case (n, l) =>
  println(s"Instance language for n=$n:$nLine${l.mkString(nLine)}" + nLine )
}

println(s"Covering grammar consisting of all normal forms:")
val nfGrammar = time { normalFormsSipGrammar(instanceLanguages) }
//println(nfGrammar)
println(s"${nfGrammar.productions.size} productions.")

val logicalComp = lcomp(simplify(toNNF(SipGrammarMinimizationFormula(nfGrammar).coversLanguageFamily(instanceLanguages))))
println(s"Logical complexity of the minimization formula: $logicalComp")

println(s"Minimized grammar:")
val minGrammar = time { minimizeSipGrammar(nfGrammar, instanceLanguages, maxSATSolver = new QMaxSAT()) }
println(minGrammar)
println()

instanceLanguages foreach { case (n, instanceLanguage) =>
  val instanceGrammar = minGrammar.instanceGrammar(n)
  println(s"Instance language for n=$n covered? " + (instanceLanguage.toSet diff instanceGrammar.language).isEmpty)
//  println(s"Instance grammar:" + nLine + "$instanceGrammar")
}
