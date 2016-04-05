package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic.tactics._
import at.logic.gapt.proofs.lk.{ LKProof, TheoryAxiom }

import scalaz._
import Scalaz._

package object gaptic {
  // LK Tactics

  def axiomLog = LogicalAxiomTactic

  def axiomTop = TopAxiomTactic

  def axiomBot = BottomAxiomTactic

  def axiomRefl = ReflexivityAxiomTactic

  def refl = ReflexivityAxiomTactic

  def trivial = axiomTop orElse axiomBot orElse axiomRefl orElse axiomLog

  def negL( applyToLabel: String ) = new NegLeftTactic( OnLabel( applyToLabel ) )

  def negL = new NegLeftTactic()

  def negR( applyToLabel: String ) = new NegRightTactic( OnLabel( applyToLabel ) )

  def negR = new NegRightTactic()

  def andL( applyToLabel: String ) = new AndLeftTactic( OnLabel( applyToLabel ) )

  def andL = new AndLeftTactic()

  def andR( applyToLabel: String ) = new AndRightTactic( OnLabel( applyToLabel ) )

  def andR = new AndRightTactic()

  def orL( applyToLabel: String ) = new OrLeftTactic( OnLabel( applyToLabel ) )

  def orL = new OrLeftTactic()

  def orR( applyToLabel: String ) = new OrRightTactic( OnLabel( applyToLabel ) )

  def orR = new OrRightTactic()

  def impL( applyToLabel: String ) = new ImpLeftTactic( OnLabel( applyToLabel ) )

  def impL = new ImpLeftTactic()

  def impR( applyToLabel: String ) = new ImpRightTactic( OnLabel( applyToLabel ) )

  def impR = new ImpRightTactic()

  def exL( applyToLabel: String, eigenVariable: Var ) = new ExistsLeftTactic( OnLabel( applyToLabel ), Some( eigenVariable ) )

  def exL( eigenVariable: Var ) = new ExistsLeftTactic( eigenVariable = Some( eigenVariable ) )

  def exL( applyToLabel: String ) = new ExistsLeftTactic( OnLabel( applyToLabel ) )

  def exL = new ExistsLeftTactic()

  def exR( applyToLabel: String, term: LambdaExpression, terms: LambdaExpression* ) = new ExistsRightTactic( OnLabel( applyToLabel ), term +: terms, instantiateOnce = false )

  def exR( term: LambdaExpression, terms: LambdaExpression* ) = new ExistsRightTactic( UniqueFormula, term +: terms, instantiateOnce = false )

  def allL( applyToLabel: String, term: LambdaExpression, terms: LambdaExpression* ) = new ForallLeftTactic( OnLabel( applyToLabel ), term +: terms, instantiateOnce = false )

  def allL( term: LambdaExpression, terms: LambdaExpression* ) = new ForallLeftTactic( UniqueFormula, term +: terms, instantiateOnce = false )

  def allR( applyToLabel: String, eigenVariable: Var ) = new ForallRightTactic( OnLabel( applyToLabel ), Some( eigenVariable ) )

  def allR( eigenVariable: Var ) = new ForallRightTactic( eigenVariable = Some( eigenVariable ) )

  def allR( applyToLabel: String ) = new ForallRightTactic( OnLabel( applyToLabel ) )

  def allR = new ForallRightTactic()

  def cut( c: String, h: HOLFormula ) = CutTactic( c, h )

  def eql( eq: String, fm: String ) = EqualityTactic( eq, fm )

  def induction( implicit ctx: Context ) = InductionTactic( UniqueFormula )
  def induction( label: String )( implicit ctx: Context ) = InductionTactic( OnLabel( label ) )

  // Meta

  def insert( proof: LKProof ) = InsertTactic( proof )

  def include( label: String, proof: LKProof ): Tactical[Unit] =
    for {
      goal <- currentGoal
      diff = proof.conclusion diff goal.conclusion
      cutFormula = diff.toDisjunction
      _ <- cut( label, cutFormula )
      _ <- insert( proof )
    } yield ()

  def theory( implicit ctx: Context ): Tactical[Unit] =
    for {
      goal <- currentGoal
      theoryAxiom <- ctx.theory( goal.conclusion collect { case a: HOLAtom => a } ).
        toTactical( "does not follow from theory" )
      _ <- insert( theoryAxiom )
    } yield ()

  def repeat[T]( t: Tactical[T] ) = RepeatTactic( t )

  @deprecated( "Proof not finished!", since = "the dawn of time" )
  def sorry = insert( TheoryAxiom( Clause() ) )
  def fail = new Tactical[Nothing] {
    def apply( proofState: ProofState ): ValidationNel[TacticalFailure, ( Nothing, ProofState )] =
      TacticalFailure( this, None, "explicit fail" ).failureNel
    override def toString = "fail"
  }

  // Complex

  def decompose = DecomposeTactic

  def destruct( label: String ) = DestructTactic( label )

  def chain( h: String ) = ChainTactic( h )

  def prop = PropTactic

  def prover9 = Prover9Tactic
  def escargot = EscargotTactic

  /**
   * Lets you "forget" a sequence of formulas, i.e. the tactics version of the weakening rule.
   *
   * @param ls A sequence of labels L,,1,,,..., L,,n,,.
   * @return The tactical
   *           (WeakeningLeftTactic(L,,1,,) orElse WeakeningRightTactic(L,,1,,)) andThen ... andThen (WeakeningLeftTactic(L,,n,,) orElse WeakeningRightTactic(L,,n,,))
   *
   */
  def forget( ls: String* ): Tactical[Unit] = ls.foldLeft[Tactical[Unit]]( SkipTactical ) { ( acc, l ) =>
    acc andThen ( WeakeningLeftTactic( l ) orElse WeakeningRightTactic( l ) )
  }

  def focus( indexOfSubGoal: Int ) = new FocusTactical( Left( indexOfSubGoal ) )
  def focus( indexOfSubGoal: OpenAssumptionIndex ) = new FocusTactical( Right( indexOfSubGoal ) )

  def rewrite = RewriteTactic( equations = Seq(), target = None, once = true )

  def unfold( definition: String, definitions: String* )( implicit ctx: Context ) =
    UnfoldTacticHelper( definition, definitions )

  def currentGoal: Tactic[OpenAssumption] = new Tactic[OpenAssumption] {
    def apply( goal: OpenAssumption ) = ( goal -> goal ).success
  }

  implicit object TacticalMonad extends Monad[Tactical] {
    def point[A]( a: => A ): Tactical[A] = new Tactical[A] {
      def apply( proofState: ProofState ) = ( a -> proofState ).success
    }

    def bind[A, B]( fa: Tactical[A] )( f: A => Tactical[B] ): Tactical[B] =
      fa flatMap f
  }

  implicit class TacticalOptionOps[T]( option: Option[T] ) {
    def toTactical( errorMsg: String ): Tactical[T] = new Tactical[T] {
      override def apply( proofState: ProofState ) =
        option match {
          case None          => TacticalFailure( this, None, errorMsg ).failureNel
          case Some( value ) => ( value -> proofState ).success
        }

      override def toString = s"$option.toTactical"
    }
  }
}
