package gapt.proofs.context.update

import gapt.expr.Const
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.expr.util.typeVariables
import gapt.proofs.context.Context
import gapt.proofs.context.facet.Constants
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.context.State
import gapt.proofs.context.facet.BaseTypes

/** Inductive base type with constructors. */
case class InductiveType( ty: TBase, constructors: Vector[Const] ) extends TypeDefinition {

  val params: List[TVar] =
    ty.params.map( _.asInstanceOf[TVar] )

  val baseCases = constructors.find {
    case Const( _, FunctionType( _, argTys ), _ ) =>
      !argTys.contains( ty )
  }

  requireConstructorsToBeConstructorsForType()
  requireDistinctConstructorNames()
  requireAtLeastOneBaseCase()

  override def apply( ctx: Context ): State = {
    require( !ctx.isType( ty ), s"Type $ty already defined" )
    for ( Const( ctr, FunctionType( _, fieldTys ), ctrPs ) <- constructors ) {
      require( ctx.constant( ctr ).isEmpty, s"Constructor $ctr is already a declared constant" )
      for ( fieldTy <- fieldTys ) {
        if ( fieldTy == ty ) {
          // positive occurrence of the inductive type
        } else {
          ctx.check( fieldTy )
        }
      }
    }
    ctx.state.update[BaseTypes]( _ + ty )
      .update[Constants]( _ ++ constructors )
      .update[StructurallyInductiveTypes]( _ + ( ty.name, constructors ) )
  }

  private def requireConstructorsToBeConstructorsForType(): Unit =
    for ( constr <- constructors ) {
      val FunctionType( ty_, _ ) = constr.ty
      require(
        ty == ty_,
        s"Base type $ty and type constructor $constr don't agree." )
      require( constr.params == params )
      require( typeVariables( constr ) subsetOf params.toSet )
    }

  private def requireDistinctConstructorNames(): Unit =
    require(
      constructors.map( _.name ) == constructors.map( _.name ).distinct,
      s"Names of type constructors are not distinct." )

  private def requireAtLeastOneBaseCase(): Unit =
    require(
      baseCases.nonEmpty,
      s"Inductive type is empty, all of the constructors are recursive: ${constructors.mkString( ", " )}" )
}

object InductiveType {
  def apply( ty: Ty, constructors: Const* ): InductiveType =
    InductiveType( ty.asInstanceOf[TBase], constructors.toVector )
  def apply( tyName: String, constructors: Const* ): InductiveType =
    InductiveType( TBase( tyName ), constructors: _* )
}