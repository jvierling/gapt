package at.logic.gapt.prooftool

import java.awt.{ Dimension, Graphics }
import javax.swing.{ JComponent, JLayer }
import javax.swing.plaf.LayerUI

import scala.swing.Graphics2D

class ZoomUI extends LayerUI[JComponent] {
  var zoom: Double = 1

  override def paint( g: Graphics, c: JComponent ) = {
    val g2 = g.create().asInstanceOf[Graphics2D]
    g2.scale( zoom, zoom )
    super.paint( g2, c )
    g2.dispose()
  }

  override def installUI( c: JComponent ) = {
    super.installUI( c )
    import java.awt.AWTEvent._
    c.asInstanceOf[JLayer[_]].setLayerEventMask( MOUSE_EVENT_MASK | ACTION_EVENT_MASK | MOUSE_MOTION_EVENT_MASK )
  }

  override def uninstallUI( c: JComponent ) = {
    c.asInstanceOf[JLayer[_]].setLayerEventMask( 0 )
    super.uninstallUI( c )
  }

  override def doLayout( l: JLayer[_ <: JComponent] ) = {
    if ( l.getView != null ) l.getView.setBounds( 0, 0, ( l.getWidth / zoom ).toInt, ( l.getHeight / zoom ).toInt )
    if ( l.getGlassPane != null ) l.getGlassPane.setBounds( 0, 0, ( l.getWidth / zoom ).toInt, ( l.getHeight / zoom ).toInt )
  }

  private def scaleByZoom( d: Dimension ) = { d.setSize( d.getWidth * zoom, d.getHeight * zoom ); d }
  override def getPreferredSize( c: JComponent ) = scaleByZoom( super.getPreferredSize( c ) )
  override def getMinimumSize( c: JComponent ) = scaleByZoom( super.getMinimumSize( c ) )
  override def getMaximumSize( c: JComponent ) = scaleByZoom( super.getMaximumSize( c ) )
}
