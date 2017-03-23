package at.logic.gapt.provers.viper.grammars

import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.expr.{ Expr, TBase }
import at.logic.gapt.proofs.Context
import cats.instances.list._
import cats.syntax.traverse._

import scala.collection.mutable
import scala.util.Random

trait InstanceTermGenerator {
  def generate( lower: Float, upper: Float, num: Int ): Set[List[Expr]]
}
class RandomInstanceGenerator( val paramTys: List[TBase], implicit val ctx: Context ) extends InstanceTermGenerator {
  def generate( lower: Float, upper: Float, num: Int ): Set[List[Expr]] = {
    var ttl = num * 10
    val instances = mutable.Set[List[Expr]]()
    while ( instances.size < num && ttl > 0 ) {
      ttl -= 1
      instances += randomInstance.generate( paramTys, x => lower <= x && x <= upper )
    }
    instances.toSet
  }
}
class EnumeratingInstanceGenerator( val paramTys: List[TBase], implicit val ctx: Context ) extends InstanceTermGenerator {
  val terms = enumerateTerms.asStream.take( 10000 ).map( t => t -> folTermSize( t ) )

  override def generate( lower: Float, upper: Float, num: Int ): Set[List[Expr]] =
    Random.shuffle( paramTys.traverse( t =>
      terms.view.filter( _._1.ty == t ).takeWhile( _._2 <= upper ).toList ).
      filter( _.view.map( _._2 ).sum >= lower ) ).take( num ).map( _.map( _._1 ) ).toSet
}
