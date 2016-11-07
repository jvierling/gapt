package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.{ All, And, HOLFormula, Polarity, clauseSubsumption, freeVariables }
import at.logic.gapt.expr.hol.{ CNFp, containsStrongQuantifier, isPrenex }
import at.logic.gapt.proofs.OccConnector
import cats.syntax.flatMap._

import scala.reflect.ClassTag
import scalaz.{ -\/, \/- }

/**
 * Recursively traverses an LK proof, applying a transformation at each level.
 *
 * The implementation is very much inspired by "Scrap Your Boilerplate" (http://research.microsoft.com/en-us/um/people/simonpj/papers/hmap/).
 */
object Traversal {
  type ProofWithConnector = ( LKProof, OccConnector[HOLFormula] )
  type ProofTrans[T <: LKProof] = T => ProofWithConnector

  /**
   * Lifts a transformation from one that only works on proofs of type T to one that works on any LKProof.
   *
   * @param f A proof transformation defined on T.
   * @return A new proof transformation defined on LKProofs that is equal to f on T and the identity otherwise.
   */
  implicit def lift2LKProof[T <: LKProof: ClassTag]( f: ProofTrans[T] ): ProofTrans[LKProof] = {
    case t: T => f( t )
    case p    => ( p, OccConnector( p.endSequent ) )
  }

  /**
   * Applies a proof transformation to the subproofs of the given proofs and then reconstructs it.
   * @param f The proof transformation to be applied.
   */
  def recurseOneLevel( f: ProofTrans[LKProof] ): ProofTrans[LKProof] = {

    /**
     * Applies f to the subproofs of proof, then uses the constructor function to rebuild proof correctly.
     */
    def applyAndReconstruct( proof: LKProof )( constructor: Seq[ProofWithConnector] => LKProof ): ProofWithConnector = {
      val visitedChildren = proof.immediateSubProofs map f
      val newProof = constructor( visitedChildren )
      val conn = ( newProof.occConnectors, visitedChildren, proof.occConnectors ).zipped.map( _ * _._2 * _.inv ).reduce( _ + _ )
      ( newProof, conn )
    }

    {

      // Initial sequents
      case p: InitialSequent => p -> OccConnector( p.endSequent )

      // Structural rules
      case p @ WeakeningLeftRule( s, form ) =>
        val ( pNew, cNew ) = applyAndReconstruct( p ) {
          case Seq( ( sp, _ ) ) => WeakeningLeftRule( sp, form )
        }
        ( pNew, cNew + ( pNew.mainIndices( 0 ), p.mainIndices( 0 ) ) ) // We have to manually add the connection between the weak formulas.
      case p @ WeakeningRightRule( s, form ) =>
        val ( pNew, cNew ) = applyAndReconstruct( p ) {
          case Seq( ( sp, _ ) ) => WeakeningRightRule( sp, form )
        }
        ( pNew, cNew + ( pNew.mainIndices( 0 ), p.mainIndices( 0 ) ) ) // We have to manually add the connection between the weak formulas.
      case p @ ContractionLeftRule( s, a1, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ContractionLeftRule( sp, sc.child( a1 ), sc.child( a2 ) )
      }
      case p @ ContractionRightRule( s, a1, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ContractionRightRule( sp, sc.child( a1 ), sc.child( a2 ) )
      }
      case p @ CutRule( s1, a1, s2, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp1, sc1 ), ( sp2, sc2 ) ) => CutRule( sp1, sc1.child( a1 ), sp2, sc2.child( a2 ) )
      }

      // Propositional rules
      case p @ NegLeftRule( s, a ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => NegLeftRule( sp, sc.child( a ) )
      }
      case p @ NegRightRule( s, a ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => NegRightRule( sp, sc.child( a ) )
      }
      case p @ AndLeftRule( s, a1, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => AndLeftRule( sp, sc.child( a1 ), sc.child( a2 ) )
      }
      case p @ AndRightRule( s1, a1, s2, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp1, sc1 ), ( sp2, sc2 ) ) => AndRightRule( sp1, sc1.child( a1 ), sp2, sc2.child( a2 ) )
      }
      case p @ OrLeftRule( s1, a1, s2, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp1, sc1 ), ( sp2, sc2 ) ) => OrLeftRule( sp1, sc1.child( a1 ), sp2, sc2.child( a2 ) )
      }
      case p @ OrRightRule( s, a1, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => OrRightRule( sp, sc.child( a1 ), sc.child( a2 ) )
      }
      case p @ ImpLeftRule( s1, a1, s2, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp1, sc1 ), ( sp2, sc2 ) ) => ImpLeftRule( sp1, sc1.child( a1 ), sp2, sc2.child( a2 ) )
      }
      case p @ ImpRightRule( s, a1, a2 ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ImpRightRule( sp, sc.child( a1 ), sc.child( a2 ) )
      }

      // Quantifier rules
      case p @ ForallLeftRule( s, a, form, term, v ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ForallLeftRule( sp, sc.child( a ), form, term, v )
      }
      case p @ ForallRightRule( s, a, eigen, quant ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ForallRightRule( sp, sc.child( a ), eigen, quant )
      }
      case p @ ForallSkRightRule( s, a, main, term, defi ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ForallSkRightRule( sp, sc.child( a ), main, term, defi )
      }
      case p @ ExistsLeftRule( s, a, eigen, quant ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ExistsLeftRule( sp, sc.child( a ), eigen, quant )
      }
      case p @ ExistsSkLeftRule( s, a, main, term, defi ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ExistsSkLeftRule( sp, sc.child( a ), main, term, defi )
      }
      case p @ ExistsRightRule( s, a, form, term, v ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => ExistsRightRule( sp, sc.child( a ), form, term, v )
      }

      // Equality rules
      case p @ EqualityLeftRule( s, eq, a, cont ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => EqualityLeftRule( sp, sc.child( eq ), sc.child( a ), cont )
      }
      case p @ EqualityRightRule( s, eq, a, cont ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => EqualityRightRule( sp, sc.child( eq ), sc.child( a ), cont )
      }

      // Induction rule
      case p @ InductionRule( cases, formula, term ) => applyAndReconstruct( p ) { subProofs =>
        InductionRule(
          for ( ( c, ( subProof, subConn ) ) <- cases zip subProofs )
            yield InductionCase( subProof, c.constructor, c.hypotheses map subConn.child, c.eigenVars, subConn.child( c.conclusion ) ),
          formula, term
        )
      }

      // Definition rules
      case p @ DefinitionLeftRule( s, a, d, c ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => DefinitionLeftRule( sp, sc.child( a ), d, c )
      }
      case p @ DefinitionRightRule( s, a, d, c ) => applyAndReconstruct( p ) {
        case Seq( ( sp, sc ) ) => DefinitionRightRule( sp, sc.child( a ), d, c )
      }
    }
  }

  /**
   *
   * @param f A proof transformation.
   * @return A new proof transformation f' that recursively applies f at every level of a proof.
   */
  def everywhere( f: ProofTrans[LKProof] ): ProofTrans[LKProof] = { p =>
    val ( subP, subC ) = recurseOneLevel( everywhere( f ) )( p )
    val ( pNew, cNew ) = f( subP )

    ( pNew, cNew * subC )
  }

  /**
   *
   * @param f A proof transformation.
   * @return A new proof transformation f' that recursively applies f at every level of a proof and performs all possible
   *         contractions on new formulas after each step.
   */
  def everywhereWithContractions( f: ProofTrans[LKProof] ): ProofTrans[LKProof] = everywhere( contractAfter( f ) )

  /**
   * Transforms a proof transformation by inserting contractions after it.
   * Only formula occurrences that were not in the old proof -- i.e., that have been added by the transformation -- are contracted.
   * @param transformation The transformation after which contractions should be inserted.
   * @return A new transformation that behaves the same as the old one, but contracts all duplicate new formulas at the end.
   */
  def contractAfter( transformation: ProofTrans[LKProof] ): ProofTrans[LKProof] = { proof =>
    val ( subProof, subConn ) = transformation( proof )

    val newFormulas = subProof.endSequent.indicesSequent
      .filter { subConn.parents( _ ).isEmpty } // Formula occurrences that were not in the old proof
      .groupBy( subProof.endSequent( _ ) ) // Group them by formula
      .filterNot( _._2.length < 2 ) // Take only the formulas with at least two occurrences
      .map { _._2 } // Take only the indices

    val ( leftProof, leftConn ) = newFormulas.antecedent.foldLeft( ( subProof, OccConnector( subProof.endSequent ) ) ) { ( acc, indices ) =>
      val ( p, c ) = acc
      val ( pNew, cNew ) = ContractionLeftMacroRule.withOccConnector( p, indices map { c.child } )
      ( pNew, cNew * c )
    }

    val ( rightProof, rightConn ) = newFormulas.succedent.foldLeft( ( leftProof, leftConn ) ) { ( acc, indices ) =>
      val ( p, c ) = acc
      val ( pNew, cNew ) = ContractionRightMacroRule.withOccConnector( p, indices map { c.child } )
      ( pNew, cNew * c )
    }

    ( rightProof, rightConn * subConn )
  }
}

/**
 * An adaptation of [[at.logic.gapt.proofs.lk.makeTheoryAxiomsExplicit]] to the "Scrap Your Boilerplate" method.
 */
object explicitTheoryAxioms {
  import Traversal._

  def visitTheoryAxiom( formulas: Seq[HOLFormula] ): ProofTrans[TheoryAxiom] = { proof =>

    val TheoryAxiom( sequent ) = proof
    formulas match {
      case Seq() => ( proof, OccConnector( sequent ) )

      case formula +: rest =>
        require( isPrenex( formula ), s"Formula $formula is not prenex." )
        require( !containsStrongQuantifier( formula, Polarity.InAntecedent ), s"Formula $formula contains strong quantifiers." )
        require( freeVariables( formula ).isEmpty, s"Formula $formula is not fully quantified." )

        val All.Block( vars, matrix ) = formula
        val cnf = CNFp( matrix )
        val cnfFormula = And( cnf map {
          _.toDisjunction
        } )
        val subs = cnf map {
          clauseSubsumption( _, sequent )
        }
        val maybeSub = subs.find( _.nonEmpty )

        maybeSub match {
          case Some( Some( sub ) ) =>
            val terms = for ( x <- vars ) yield sub.map.getOrElse( x, x )

            val maybeProof = for {
              subroof <- solvePropositional( sub( matrix ) +: sequent )
            } yield ForallLeftBlock( subroof, formula, terms )

            val subProof = maybeProof match {
              case \/-( p )   => p
              case -\/( seq ) => throw new Exception( s"Sequent $seq is not provable." )
            }
            ( subProof, OccConnector.findEquals( subProof.endSequent, sequent ) )

          case _ => visitTheoryAxiom( rest )( proof )
        }
    }
  }
  def apply( formulas: Seq[HOLFormula] ): ProofTrans[LKProof] = {
    everywhereWithContractions( visitTheoryAxiom( formulas ) )
  }
}