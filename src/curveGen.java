
import java.awt.event.*;

import com.jogamp.opengl.*;
import com.jogamp.opengl.awt.GLCanvas;
import com.jogamp.nativewindow.ScalableSurface;

import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.vecmath.Point2f;

import java.util.ArrayList;
import java.util.Scanner;
import java.io.*;
import javax.vecmath.Matrix3f;
import javax.vecmath.Vector3f;

public class curveGen extends JFrame implements GLEventListener, KeyListener, MouseListener, MouseMotionListener, ActionListener {

    /* GL related variables */
    private final GLCanvas canvas;
    private GL2 gl;

    private int winW = 600, winH = 600;

    private static final int Quadratic = 1, CubicBezier = 2, Bspline = 3;
    /* initial curve type: Quadratic */
    private int curve_type = Quadratic;
    /* number of line segments used to approximate curves */
    private int nsegment = 32;
    /* toggle between closing a curve. only applicable to Bspline */
    private boolean close_curve = false;
    /* toggle showing of control point line */
    private boolean show_control_line = true;

    /* control_pts is an array that stores a list of the control points
     * each element is a 2D point. control points can be created using
     * the GUI interface, or loaded from a disk file
     */
    private ArrayList<Point2f> control_pts = new ArrayList<Point2f>();
    /* curve_pts is an array that stores points representing the quadratic, Bspline
     * or cubic Bezier curve, and it is generated by your code.
     */
    private ArrayList<Point2f> curve_pts = new ArrayList<Point2f>();
    /* selected_point keeps track of the currect control point selected by mouse
     * -1 means no point is selected currently
     */
    private int selected_point = -1;

    private void drawControlLines() {
        int i;
        for (i = 0; i < control_pts.size(); i++) {
            Point2f pt = control_pts.get(i);
            drawRectangle(pt.x - 0.008f, pt.y - 0.008f, pt.x + 0.008f, pt.y + 0.008f, 1, 0, 0);
        }
        for (i = 0; i < control_pts.size() - 1; i++) {
            Point2f pt1 = control_pts.get(i);
            Point2f pt2 = control_pts.get(i + 1);
            drawLine(pt1.x, pt1.y, pt2.x, pt2.y, 0, 0, 1);
        }
    }

    public static void main(String args[]) {
        if (args.length == 1) {
            // if an input filename is given, try to load control points from the file
            new curveGen(args[0]);
        } else {
            new curveGen(null);
        }
    }

    private void drawLine(float x1, float y1, float x2, float y2, float red, float green, float blue) {
        gl.glColor3f(red, green, blue);
        gl.glBegin(GL2.GL_LINES);
        gl.glVertex2f(x1, y1);
        gl.glVertex2f(x2, y2);
        gl.glEnd();
    }

    private void drawRectangle(float xmin, float ymin, float xmax, float ymax, float red, float green, float blue) {
        gl.glColor3f(red, green, blue);
        gl.glBegin(GL2.GL_QUADS);
        gl.glVertex2f(xmin, ymin);
        gl.glVertex2f(xmin, ymax);
        gl.glVertex2f(xmax, ymax);
        gl.glVertex2f(xmax, ymin);
        gl.glEnd();
    }

    /* load control points from a disk file */
    private void loadPoints(String filename) {
        File file = null;
        Scanner scanner = null;
        try {
            file = new File(filename);
            scanner = new Scanner(file);
        } catch (IOException e) {
            System.out.println("Error reading from file " + filename);
            System.exit(0);
        }
        float x, y;
        while (scanner.hasNext()) {
            x = scanner.nextFloat();
            y = scanner.nextFloat();
            control_pts.add(new Point2f(x, y));
        }
        System.out.println("Read " + control_pts.size()
            + " points from file " + filename);
        scanner.close();
    }

    /* save control points and curve points to disk files
     * both files have the extension name '.pts'
     * you will input a filename, say, it's 'cup', then
     * the control points will be saved to 'cup.pts',
     * and the curve points will be saved to 'cup_curve.pts'.
     */
    private void savePoints() {
        String curvename = JOptionPane.showInputDialog(this, "Input a name of the curve to save", "mycurve");
        if (curvename == null) {
            return;
        }
        int i;
        // save the control points to curvename.pts
        FileOutputStream file = null;
        PrintStream output = null;
        try {
            file = new FileOutputStream(curvename + ".pts");
            output = new PrintStream(file);
        } catch (IOException e) {
            System.out.println("Error writing to file " + curvename + ".pts");
            return;
        }
        for (i = 0; i < control_pts.size(); i++) {
            output.println(control_pts.get(i).x + " " + control_pts.get(i).y);
        }
        output.close();

        try {
            file = new FileOutputStream(curvename + "_curve.pts");
            output = new PrintStream(file);
        } catch (IOException e) {
            System.out.println("Error writing to file " + curvename + "_curve.pts");
            return;
        }
        for (i = 0; i < curve_pts.size(); i++) {
            output.println(curve_pts.get(i).x + " " + curve_pts.get(i).y);
        }
        output.close();
    }

    /* creates OpenGL window */
    public curveGen(String inputFilename) {
        super("Assignment 4 -- Curve Generator");
        final GLProfile glprofile = GLProfile.getMaxFixedFunc(true);
        GLCapabilities glcapabilities = new GLCapabilities(glprofile);
        canvas = new GLCanvas(glcapabilities);        
        canvas.setSurfaceScale(new float[]{ScalableSurface.IDENTITY_PIXELSCALE, ScalableSurface.IDENTITY_PIXELSCALE}); // potential fix for Retina Displays		
        canvas.addGLEventListener(this);
        canvas.addKeyListener(this);
        canvas.addMouseListener(this);
        canvas.addMouseMotionListener(this);
        getContentPane().add(canvas);
        setSize(winW, winH);
        setLocationRelativeTo(null);
        setDefaultCloseOperation(EXIT_ON_CLOSE);
        setVisible(true);
        canvas.requestFocus();
        if (inputFilename != null) {
            loadPoints(inputFilename);
        }
    }

    private void drawQuadraticInterp() 
    {
	// ***** YOUR WORK HERE *****
        /* computes and draws piecewise quadratic polynomial curves
         * each piece of the curve is approximated by nsegment line segments,
         * these line segments should be drawn to screen by calling drawLine
         * 
         * remember that you also have to store your generated curve points
         * in the 'curve_pts' array, so that the curve can be saved to a disk file later
         * 
         * if there are less than 3 interpolating points, return immediately
         */
        Matrix3f basisMatrix = new Matrix3f(1, 0, 0, -3, 4, -1, 2, -4, 2);
		int npts = control_pts.size();
		int point_index = 0;
        if (npts < 3)
            return;
        curve_pts.clear();
        System.out.println("Generating Quadratic points");
        while (point_index < npts - 2) {
            for (float u = 0; u <= 1; u+= 1.0f/nsegment) {
                Point2f q = new Point2f();
                for (int i = 0; i<=2; i++) {
                    Vector3f temp = new Vector3f();
                    basisMatrix.getColumn(i, temp);
                    float b_i = (new Vector3f(1, u, u*u)).dot(temp);
                    q.x += b_i * control_pts.get(point_index + i).x;
                    q.y += b_i * control_pts.get(point_index + i).y;
                }
                curve_pts.add(q);
            }
            point_index += 2;
        }
        System.out.println("Drawing curve");
        for (int i = 0; i < curve_pts.size() - 1; i ++) {
                Point2f tempPoint1 = curve_pts.get(i);
                Point2f tempPoint2 = curve_pts.get(i+1);
                drawLine(tempPoint1.x, tempPoint1.y, tempPoint2.x, tempPoint2.y, 0,1,0);
        }

    }

    private void drawCubicBezier() {
	// ***** YOUR WORK HERE *****
	/* computes and draws piecewise cubic Bezier curves
         * each *piece* of the curve is approximated by nsegment line segments,
         * these line segments should be drawn to screen by calling drawLine
         * 
         * remember that you also have to store your generated curve points
         * in the 'curve_pts' array, so that the curve can be saved to a disk file later
         * 
         * if there are less than 4 control points, return immediately
         */
    }

    private void drawBspline() {
        // ***** YOUR WORK HERE *****
        /* computes and draws piecewise cubic Bspline curves
         * each *piece* of the curve (computed from four neighboring control points)
         * is approximated by nsegment line segments.
         * these line segments are then drawn to screen by calling drawLine
         * 		 
         * note that if boolean variable close_curve is true,
         * you should produce a closed piecewise Bspline curve
         *
		 * remember that the curve should always start from the first point and 
		 * end at the last point 
		 *
         * remember that you also have to store your generated curve points
         * in the curve_pts array, so that the curve can be saved to a disk file later
         * 
         * if there are less than 4 control points, return immediately
         */
    }

    /* gl display function */
    public void display(GLAutoDrawable drawable) {
        gl.glClear(GL2.GL_COLOR_BUFFER_BIT);
        if (show_control_line) {
            drawControlLines();
        }
        switch (curve_type) {
            case Quadratic:
                drawQuadraticInterp();
                break;
            case CubicBezier:
                drawCubicBezier();
                break;
            case Bspline:
                drawBspline();
                break;
        }
    }

    /* initialize GL */
    public void init(GLAutoDrawable drawable) {
        gl = drawable.getGL().getGL2();

        gl.glClearColor(.3f, .3f, .3f, 1f);
        gl.glClearDepth(1.0f);

        gl.glMatrixMode(GL2.GL_PROJECTION);
        gl.glLoadIdentity();
        gl.glOrtho(0, 1, 0, 1, -10, 10);
        gl.glMatrixMode(GL2.GL_MODELVIEW);
    }

    /* mouse and keyboard callback functions */
    public void reshape(GLAutoDrawable drawable, int x, int y, int width, int height) {
        winW = width;
        winH = height;

        gl.glViewport(0, 0, width, height);
    }

    public void mousePressed(MouseEvent e) {

        /* normalize the mouse position to be between [0, 1] x [0, 1] */
        float x = (float) e.getX() / (float) winW;
        float y = 1.0f - (float) e.getY() / (float) winH;

        /* if mouse left button is pressed */
        if (e.getButton() == MouseEvent.BUTTON1) {
            /* detect whether the mouse clicked on any existing control point */
            int i;
            selected_point = -1;
            for (i = 0; i < control_pts.size(); i++) {
                Point2f pt = control_pts.get(i);
                if (Math.abs(pt.x - x) < 0.008f && Math.abs(pt.y - y) < 0.008f) {
                    selected_point = i;
                }
            }
            /* if CTRL is pressed, add a point */
            if ((e.getModifiers() & InputEvent.CTRL_MASK) != 0) {
                if (selected_point == -1) {
                    control_pts.add(new Point2f(x, y));
                }
            } /* if SHIFT is pressed, and a valid point is selected, then delete the point */ else if ((e.getModifiers() & InputEvent.SHIFT_MASK) != 0) {
                if (selected_point >= 0) {
                    control_pts.remove(selected_point);
                    selected_point = -1;
                }
            }
            canvas.display();
        }
    }

    /* if mouse is dragging on an existing control point, move that point */
    public void mouseDragged(MouseEvent e) {
        float x = (float) e.getX() / (float) winW;
        float y = 1.0f - (float) e.getY() / (float) winH;
        if (selected_point >= 0) {
            control_pts.get(selected_point).x = x;
            control_pts.get(selected_point).y = y;
            canvas.display();
        }
    }

    public void keyPressed(KeyEvent e) {
        switch (e.getKeyCode()) {
            case KeyEvent.VK_ESCAPE:
            case KeyEvent.VK_Q:
                System.exit(0);
                break;
            // press 'e' to clear all control points
            case KeyEvent.VK_E:
                control_pts.clear();
                canvas.display();
                break;
            // press '1' to select quadratic curve, '2' for cubic Bezier curve, '3' for Bspline
            case KeyEvent.VK_1:
                curve_type = Quadratic;
                canvas.display();
                break;                
            case KeyEvent.VK_2:
                curve_type = CubicBezier;
                canvas.display();
                break;
            case KeyEvent.VK_3:
                curve_type = Bspline;
                canvas.display();
                break;
            // press '+' or '-' to increase or decrease nsegment
            case KeyEvent.VK_ADD:
            case KeyEvent.VK_EQUALS:
                nsegment = nsegment + 1;
                canvas.display();
                break;
            case KeyEvent.VK_MINUS:
                if (nsegment > 1) {
                    nsegment = nsegment - 1;
                }
                canvas.display();
                break;
            // press 'c' to toggle closing curve for B-splines
            case KeyEvent.VK_C:
                close_curve = !close_curve;
                canvas.display();
                break;
            // press 'l' to toggle showing control line
            case KeyEvent.VK_L:
                show_control_line = !show_control_line;
                canvas.display();
                break;
            // press 's' to save points
            case KeyEvent.VK_S:
                savePoints();
                canvas.display();
                break;
        }
    }

    // these event functions are not used for this assignment
    public void dispose(GLAutoDrawable glautodrawable) {
    }
    
    public void displayChanged(GLAutoDrawable drawable, boolean modeChanged, boolean deviceChanged) {
    }

    public void mouseReleased(MouseEvent e) {
    }

    public void keyTyped(KeyEvent e) {
    }

    public void keyReleased(KeyEvent e) {
    }

    public void mouseMoved(MouseEvent e) {
    }

    public void actionPerformed(ActionEvent e) {
    }

    public void mouseClicked(MouseEvent e) {
    }

    public void mouseEntered(MouseEvent e) {
    }

    public void mouseExited(MouseEvent e) {
    }

}
