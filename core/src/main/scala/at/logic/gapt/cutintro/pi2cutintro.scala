package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.grammars.Pi2Grammar
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.InstanceTermEncoding

object pi2GrammarToSEHS {
  def apply( g: Pi2Grammar, encoding: InstanceTermEncoding ): Pi2SeHs = {
    Pi2SeHs(
      reducedRepresentation = Sequent(
        for ( ( g.startSymbol, rhs ) <- g.productions )
          yield if ( freeVariables( rhs ).contains( g.alpha ) )
          ( encoding.decodeToSignedFormula( rhs ), Polarity.InAntecedent )
        else
          ( -encoding.decodeToSignedFormula( rhs ), Polarity.InSuccedent )

      ),
      universalEigenvariable = g.alpha,
      existentialEigenvariables = g.betas.toList,
      substitutionsForAlpha = g.betas.map( beta => g.productions.find( _._1 == beta ).get._2 ).toList,
      substitutionsForBetaWithAlpha = g.productions.filter( _._1 == g.alpha ).map( _._2 ).toList
    )
  }
}