package at.logic.gapt.expr

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap

trait HOLFormula extends LambdaExpression

trait LogicalConstant extends Const

trait FOLExpression extends LambdaExpression {
  def renameSymbols( map: SymbolMap ): FOLExpression = NameReplacement( this, map )
}
private[expr] trait FOLLambdaTerm extends LambdaExpression {
  private[expr] def returnType: TA
  private[expr] def numberOfArguments: Int
}
trait FOLTerm extends FOLLambdaTerm with FOLExpression {
  private[expr] override val returnType = Ti
  private[expr] override val numberOfArguments = 0

  override def renameSymbols( map: SymbolMap ): FOLTerm = NameReplacement( this, map ).asInstanceOf[FOLTerm]
}
trait FOLVar extends Var with FOLTerm
trait FOLConst extends Const with FOLTerm
trait FOLFormula extends FOLLambdaTerm with HOLFormula with FOLExpression {
  private[expr] override val returnType = To
  private[expr] override val numberOfArguments = 0

  override def renameSymbols( map: SymbolMap ): FOLFormula = NameReplacement( this, map )
}
private[expr] trait FOLFormulaWithBoundVar extends LambdaExpression
trait FOLQuantifier extends LogicalConstant

private[expr] trait PropLambdaTerm extends FOLLambdaTerm {
  private[expr] override val returnType = To
}
trait PropFormula extends PropLambdaTerm with FOLFormula
trait PropConnective extends LogicalConstant with PropLambdaTerm {
  private[expr] override val returnType = To
}
trait PropAtom extends Const with PropFormula

private[expr] object determineTraits {
  private class Var_with_FOLVar( s: SymbolA, t: TA ) extends Var( s, t ) with FOLVar
  private class Var_with_HOLFormula( s: SymbolA, t: TA ) extends Var( s, t ) with HOLFormula
  def forVar( sym: SymbolA, exptype: TA ): Var = exptype match {
    case Ti => new Var_with_FOLVar( sym, exptype )
    case To => new Var_with_HOLFormula( sym, exptype )
    case _  => new Var( sym, exptype )
  }

  private class Const_with_FOLQuantifier( s: SymbolA, t: TA ) extends Const( s, t ) with FOLQuantifier
  private class Const_with_PropConnective_with_PropFormula( s: SymbolA, t: TA ) extends Const( s, t ) with PropConnective with PropFormula
  private class Const_with_FOLConst( s: SymbolA, t: TA ) extends Const( s, t ) with FOLConst
  private class Const_with_PropFormula( s: SymbolA, t: TA ) extends Const( s, t ) with PropFormula
  private class Const_with_PropConnective( s: SymbolA, t: TA, override val numberOfArguments: Int ) extends Const( s, t ) with PropConnective
  private class Const_with_PropLambdaTerm( s: SymbolA, t: TA, override val numberOfArguments: Int ) extends Const( s, t ) with PropLambdaTerm
  private class Const_with_FOLLambdaTerm( s: SymbolA, t: TA, override val returnType: TA, override val numberOfArguments: Int ) extends Const( s, t ) with FOLLambdaTerm
  def forConst( sym: SymbolA, exptype: TA ): Const = ( sym, exptype ) match {
    case ForallC( Ti ) | ExistsC( Ti ) => new Const_with_FOLQuantifier( sym, exptype )
    case AndC() | OrC() | ImpC()       => new Const_with_PropConnective( sym, exptype, 2 )
    case NegC()                        => new Const_with_PropConnective( sym, exptype, 1 )
    case TopC() | BottomC()            => new Const_with_PropConnective_with_PropFormula( sym, exptype )
    case ( _, Ti )                     => new Const_with_FOLConst( sym, exptype )
    case ( _, To )                     => new Const_with_PropFormula( sym, exptype )
    case ( _, FOLHeadType( Ti, n ) )   => new Const_with_FOLLambdaTerm( sym, exptype, Ti, n )
    case ( _, FOLHeadType( To, n ) )   => new Const_with_PropLambdaTerm( sym, exptype, n )
    case _                             => new Const( sym, exptype )
  }

  private class App_with_PropFormula( f: LambdaExpression, a: LambdaExpression ) extends App( f, a ) with PropFormula
  private class App_with_FOLTerm( f: LambdaExpression, a: LambdaExpression ) extends App( f, a ) with FOLTerm
  private class App_with_FOLFormula( f: LambdaExpression, a: LambdaExpression ) extends App( f, a ) with FOLFormula
  private class App_with_HOLFormula( f: LambdaExpression, a: LambdaExpression ) extends App( f, a ) with HOLFormula
  private class App_with_FOLLambdaTerm( f: LambdaExpression, a: LambdaExpression, override val returnType: TA, override val numberOfArguments: Int ) extends App( f, a ) with FOLLambdaTerm
  private class App_with_PropLambdaTerm( f: LambdaExpression, a: LambdaExpression, override val numberOfArguments: Int ) extends App( f, a ) with PropLambdaTerm
  def forApp( f: LambdaExpression, a: LambdaExpression ): App = ( f, a ) match {
    case ( f: PropLambdaTerm, a: PropFormula ) => f.numberOfArguments match {
      case 1 => new App_with_PropFormula( f, a )
      case n => new App_with_PropLambdaTerm( f, a, n - 1 )
    }
    case ( f: FOLLambdaTerm, a: FOLExpression ) => f.numberOfArguments match {
      case 1 => f.returnType match {
        case Ti => new App_with_FOLTerm( f, a )
        case To => new App_with_FOLFormula( f, a )
      }
      case n => new App_with_FOLLambdaTerm( f, a, f.returnType, n - 1 )
    }
    case ( f: FOLQuantifier, _ ) => a match {
      case a: FOLFormulaWithBoundVar => new App_with_FOLFormula( f, a )
      case _                         => new App_with_HOLFormula( f, a )
    }
    case _ => f.exptype match {
      case ->( _, To ) => new App_with_HOLFormula( f, a )
      case _           => new App( f, a )
    }
  }

  private class Abs_with_FOLFormulaWithBoundVar( v: Var, t: LambdaExpression ) extends Abs( v, t ) with FOLFormulaWithBoundVar
  def forAbs( v: Var, t: LambdaExpression ): Abs = ( v.exptype, t ) match {
    case ( Ti, t: FOLFormula ) => new Abs_with_FOLFormulaWithBoundVar( v, t )
    case _                     => new Abs( v, t )
  }
}

object FOLVar {
  def apply( sym: String ): FOLVar = Var( sym, Ti ).asInstanceOf[FOLVar]
  def unapply( e: LambdaExpression ) = e match {
    case Var( sym, Ti ) => Some( sym )
    case _              => None
  }
}

object FOLConst {
  def apply( sym: String ): FOLConst = FOLFunction( sym ).asInstanceOf[FOLConst]
  def unapply( e: LambdaExpression ): Option[String] = e match {
    case FOLFunction( name, List() ) => Some( name )
    case _                           => None
  }
}
