package at.logic.gapt.provers.viper.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.proofs.Context
import at.logic.gapt.utils.NameGenerator

import scala.util.Random

object randomInstance {

  def generate( tys: List[TBase] )( implicit ctx: Context ): List[Expr] = {
    val nameGen = new NameGenerator( Set() )
    tys.map( generate( _, nameGen ) )
  }
  def generate( ty: TBase )( implicit ctx: Context ): Expr = generate( ty, new NameGenerator( Set() ) )

  def generate( ty: TBase, nameGen: NameGenerator )( implicit ctx: Context ): Expr = {
    ctx.getConstructors( ty ) match {
      case None =>
        Var( nameGen freshWithIndex "x", ty )
      case Some( ctrs ) =>
        val ctr = ctrs( Random.nextInt( ctrs.size ) )
        val FunctionType( _, argTypes ) = ctr.ty
        val args = argTypes.map { at => generate( at.asInstanceOf[TBase], nameGen ) }
        ctr( args: _* )
    }
  }

  def generate( tys: List[TBase], cond: Float => Boolean )( implicit ctx: Context ): List[Expr] =
    Stream.continually( generate( tys ) ).filter( insts => cond( folTermSize( insts ).toFloat / insts.size ) ).head

}
