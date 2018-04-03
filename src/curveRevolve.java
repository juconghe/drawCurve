import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.io.*;
import java.nio.FloatBuffer;
import java.nio.IntBuffer;

import com.jogamp.opengl.*;
import com.jogamp.opengl.glu.GLU;
import com.jogamp.opengl.awt.GLCanvas;
import com.jogamp.nativewindow.ScalableSurface;

import javax.swing.JFrame;
import javax.vecmath.Point2f;
import javax.vecmath.Point3f;
import javax.vecmath.Vector3f;

import com.jogamp.common.nio.Buffers;

import java.util.ArrayList;
import java.util.Scanner;

class curveRevolve extends JFrame implements GLEventListener, KeyListener, MouseListener, MouseMotionListener, ActionListener {

	/* curve_pts stores the curve points read in from an input file */
	private static ArrayList<Point2f> curve_pts = new ArrayList<Point2f> ();
	
	/* verts and faces store the surface of revolution
	 * normals store the shading normals
	 */
	private static ArrayList<Point3f> verts = new ArrayList<Point3f> ();
	private static ArrayList<Integer> faces = new ArrayList<Integer> ();
	private static ArrayList<Vector3f> normals = new ArrayList<Vector3f> ();
	
	/* the following buffers store the same data with the ones above
	 * but they are used by glVertexPoint and glDrawElements to accelerate
	 * OpenGL rendering speed 
	 */
	private static FloatBuffer vertBuffer;
	private static IntBuffer faceBuffer;
	private static FloatBuffer normBuffer;

	/* nsegment is the number of partitions of a full rotation */
	private static int nsegment = 64;
	
	/* axis is the center axis around which the curve will be rotate */
	private static float axis = 1.0f;

	/* GL, display, model transformation, and mouse control variables */
	private final GLCanvas canvas;
	private static GL2 gl;
	private final GLU glu = new GLU();	

	private static int winW = 800, winH = 800;
	private static boolean wireframe = false;
	private static boolean cullface = false;
	private static boolean flatshade = false;
	
	private static float xpos = 0, ypos = 0, zpos = 0;
	private static float xmin, ymin, zmin;
	private static float xmax, ymax, zmax;
	private static float centerx, centery, centerz;
	private static float roth = 0, rotv = 0;
	private static float znear, zfar;
	private static int mouseX, mouseY, mouseButton;
	private static float motionSpeed, rotateSpeed;
	
	// load curve points from .pts file
	private static void loadPoints(String filename) {
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
		while(scanner.hasNext()) {
			x = scanner.nextFloat();
			y = scanner.nextFloat();
			curve_pts.add(new Point2f(x, y));
		}
		System.out.println("Read " + curve_pts.size() +
					   	" points from file " + filename);
		scanner.close();
	}

	// compute the surface of revolution
	// results are stored in 'verts' and 'faces'
	private static void computeMesh() {
		int i, j;
		int npts = curve_pts.size();
		boolean closed = false;
		float angle, vx, vy, vz;
		if (curve_pts.get(0).x == curve_pts.get(npts-1).x && 
			curve_pts.get(0).y == curve_pts.get(npts-1).y) {
			closed = true;
		}
		for (j = 0; j < nsegment; j ++) {
			for (i = 0; i < (closed ? (npts-1) : npts); i ++) {
				angle = (float)Math.PI + 2 * (float)Math.PI * j / nsegment;
				vx = (axis - curve_pts.get(i).x) * (float)Math.cos(angle);
				vy = curve_pts.get(i).y;
				vz = -(axis - curve_pts.get(i).x) * (float)Math.sin(angle);
				verts.add(new Point3f(vx, vy, vz));
			}
		}
		int v1, v2, v3, v4;
		for (j = 0; j < nsegment; j ++) {
			if (closed) {
				for (i = 0; i < npts-1; i ++) {
					v1 = j*(npts-1) + i;
					v2 = j*(npts-1) + (i+1)%(npts-1);
					v3 = ((j+1)%nsegment) * (npts-1) + (i+1)%(npts-1);
					v4 = ((j+1)%nsegment) * (npts-1) + i;	
					faces.add(v1);
					faces.add(v2);
					faces.add(v3);
					faces.add(v4);
					
				}
			} else {
				for (i = 0; i < npts-1; i ++) {
					v1 = j*npts+i;
					v2 = j*npts+i+1;
					v3 = ((j+1)%nsegment) * npts + i+1;
					v4 = ((j+1)%nsegment) * npts + i;
					faces.add(v1);
					faces.add(v2);
					faces.add(v3);
					faces.add(v4);
				}
			}
		}		
	}
	
	// find the bounding box of all vertices
	private static void computeBoundingBox() {
		xmax = xmin = verts.get(0).x;
		ymax = ymin = verts.get(0).y;
		zmax = zmin = verts.get(0).z;
		
		for (int i = 1; i < verts.size(); i ++) {
			xmax = Math.max(xmax, verts.get(i).x);
			xmin = Math.min(xmin, verts.get(i).x);
			ymax = Math.max(ymax, verts.get(i).y);
			ymin = Math.min(ymin, verts.get(i).y);
			zmax = Math.max(zmax, verts.get(i).z);
			zmin = Math.min(zmin, verts.get(i).z);			
		}
		
	}
	
	/* estimate per-vertex average normal */
	private static void estimateVertexNormal() {
		int i;
		normals.clear();
		for (i = 0; i < verts.size(); i ++) {
			normals.add(new Vector3f());
		}
		
		Vector3f e1 = new Vector3f();
		Vector3f e2 = new Vector3f();
		Vector3f tn = new Vector3f();
		for (i = 0; i < faces.size()/4; i ++) {
			// get face
			int v1 = faces.get(4*i+0);
			int v2 = faces.get(4*i+1);
			int v3 = faces.get(4*i+2);
			int v4 = faces.get(4*i+3);
			
			// compute normal for the vertex v1
			e1.sub(verts.get(v2), verts.get(v1));
			e2.sub(verts.get(v4), verts.get(v1));
			tn.cross(e1, e2);
			// add contribution to the average normal at vertex v1
			normals.get(v1).add(tn);
			
			// compute normal for the vertex v2
			e1.sub(verts.get(v3), verts.get(v2));
			e2.sub(verts.get(v1), verts.get(v2));
			tn.cross(e1, e2);
			// add contribution to the average normal at vertex v2
			normals.get(v2).add(tn);
			
			// compute normal for the vertex v3
			e1.sub(verts.get(v4), verts.get(v3));
			e2.sub(verts.get(v2), verts.get(v3));
			tn.cross(e1, e2);
			// add contribution to the average normal at vertex v3
			normals.get(v3).add(tn);			
			
			// compute normal for the vertex v1
			e1.sub(verts.get(v1), verts.get(v4));
			e2.sub(verts.get(v3), verts.get(v4));
			tn.cross(e1, e2);
			// add contribution to the average normal at vertex v1
			normals.get(v4).add(tn);			
		}
		
		// normalize
		for (i = 0; i < verts.size(); i ++) {
			normals.get(i).normalize();
		}		
	}
	
	public static void printUsage() {
		System.out.println("Usage: java curveRevolve input_curve.pts [options]");
		System.out.println("-nsegment <int>");
		System.out.println("-axis <float>");
		System.exit(1);
	}

	public curveRevolve() {
		super("Assignment 4 -- Curve Revolve");
		canvas = new GLCanvas();
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
	}
	
	public static void main(String[] args) {

		int i;
		String arg = null;
		String inputFilename = null;
		if (args.length < 1) {
			printUsage();
		}
		inputFilename = args[0];
		i = 1;
		while (i < args.length && args[i].startsWith("-")) {
			arg = args[i++];

			if (arg.equals("-nsegment")) {
				nsegment = Integer.parseInt(args[i++]);
				System.out.println("Set nsegment: " + nsegment);

			} else if (arg.equals("-axis")) {
				axis = Float.parseFloat(args[i++]);
				System.out.println("Set axis: " + axis);
			} else {
				printUsage();
			}
		}
		loadPoints(inputFilename);
		computeMesh();
		computeBoundingBox();
		estimateVertexNormal();
		
		// convert vertex and face data into buffers to improve rendering speed
                vertBuffer = Buffers.newDirectFloatBuffer(verts.size() * 3);
                normBuffer = Buffers.newDirectFloatBuffer(verts.size() * 3);
                faceBuffer = Buffers.newDirectIntBuffer(faces.size());
                
		
		for (i = 0; i < verts.size(); i ++) {
			vertBuffer.put(verts.get(i).x);
			vertBuffer.put(verts.get(i).y);
			vertBuffer.put(verts.get(i).z);
			normBuffer.put(normals.get(i).x);
			normBuffer.put(normals.get(i).y);
			normBuffer.put(normals.get(i).z);			
		}
		
		for (i = 0; i < faces.size(); i ++) {
			faceBuffer.put(faces.get(i));	
		}
		
		new curveRevolve();
	}
	
	public void init(GLAutoDrawable drawable) {
		gl = drawable.getGL().getGL2();

		initViewParameters();
		gl.glClearColor(.3f, .3f, .3f, 1f);
		gl.glClearDepth(1.0f);

		float mat_specular[] = {0.9f, 0.9f, 0.9f, 1.0f};
		float mat_diffuse[] = {0.8f, 0.5f, 0.2f, 1.0f};
		float mat_shiny[] = {40.f};
		
		gl.glEnable(GL2.GL_DEPTH_TEST);
		gl.glDepthFunc(GL2.GL_LESS);
		gl.glHint(GL2.GL_PERSPECTIVE_CORRECTION_HINT, GL2.GL_NICEST);
		
		gl.glCullFace(GL2.GL_BACK);
		gl.glEnable(GL2.GL_CULL_FACE);
		gl.glShadeModel(GL2.GL_SMOOTH);		

		gl.glMaterialfv(GL2.GL_FRONT_AND_BACK, GL2.GL_SPECULAR, mat_specular, 0);
		gl.glMaterialfv(GL2.GL_FRONT_AND_BACK, GL2.GL_DIFFUSE, mat_diffuse, 0);
		gl.glMaterialfv(GL2.GL_FRONT_AND_BACK, GL2.GL_SHININESS, mat_shiny, 0);
		
		gl.glEnable(GL2.GL_LIGHTING);
		gl.glEnable(GL2.GL_LIGHT0);		
	}
	
	public void reshape(GLAutoDrawable drawable, int x, int y, int width, int height) {
		winW = width;
		winH = height;

		gl.glViewport(0, 0, width, height);
		gl.glMatrixMode(GL2.GL_PROJECTION);
			gl.glLoadIdentity();
			glu.gluPerspective(30.f, (float)width/(float)height, znear, zfar);
		gl.glMatrixMode(GL2.GL_MODELVIEW);
	}
	
	public void mousePressed(MouseEvent e) {	
		mouseX = e.getX();
		mouseY = e.getY();
		mouseButton = e.getButton();
		canvas.display();
	}
	
	public void mouseReleased(MouseEvent e) {
		mouseButton = MouseEvent.NOBUTTON;
		canvas.display();
	}	
	
	public void mouseDragged(MouseEvent e) {
		int x = e.getX();
		int y = e.getY();
		if (mouseButton == MouseEvent.BUTTON3) {
			zpos -= (y - mouseY) * motionSpeed;
			mouseX = x;
			mouseY = y;
			canvas.display();
		} else if (mouseButton == MouseEvent.BUTTON2) {
			xpos -= (x - mouseX) * motionSpeed;
			ypos += (y - mouseY) * motionSpeed;
			mouseX = x;
			mouseY = y;
			canvas.display();
		} else if (mouseButton == MouseEvent.BUTTON1) {
			roth -= (x - mouseX) * rotateSpeed;
			rotv += (y - mouseY) * rotateSpeed;
			mouseX = x;
			mouseY = y;
			canvas.display();
		}
	}

	public void keyPressed(KeyEvent e) {
		switch(e.getKeyCode()) {
		case KeyEvent.VK_ESCAPE:
		case KeyEvent.VK_Q:
			System.exit(0);
			break;		
		case 'r':
		case 'R':
			initViewParameters();
			break;
		case 'w':
		case 'W':
			wireframe = ! wireframe;
			break;
		case 'b':
		case 'B':
			cullface = !cullface;
			break;
		case 'f':
		case 'F':
			flatshade = !flatshade;
			break;
		default:
			break;
		}
		canvas.display();
	}
	
	public void display(GLAutoDrawable drawable) {
		float lightPos[] = {0.f, 0.f, 0.f, 1.0f};
		gl.glClear(GL2.GL_COLOR_BUFFER_BIT | GL2.GL_DEPTH_BUFFER_BIT);
		
		gl.glPolygonMode(GL2.GL_FRONT_AND_BACK, wireframe ? GL2.GL_LINE : GL2.GL_FILL);	
		gl.glShadeModel(flatshade ? GL2.GL_FLAT : GL2.GL_SMOOTH);		
		if (cullface)
			gl.glEnable(GL2.GL_CULL_FACE);
		else
			gl.glDisable(GL2.GL_CULL_FACE);		
		
		gl.glLoadIdentity();
		
		gl.glLightfv(GL2.GL_LIGHT0, GL2.GL_POSITION, lightPos, 0);
		gl.glLightModeli(GL2.GL_LIGHT_MODEL_TWO_SIDE, GL2.GL_TRUE);
		
		gl.glTranslatef(-xpos, -ypos, -zpos);
		gl.glTranslatef(centerx, centery, centerz);
		gl.glRotatef(360.f - roth, 0, 1.0f, 0);
		gl.glRotatef(rotv, 1.0f, 0, 0);
		gl.glTranslatef(-centerx, -centery, -centerz);	
		
		gl.glEnableClientState(GL2.GL_VERTEX_ARRAY);
		gl.glEnableClientState(GL2.GL_NORMAL_ARRAY);
		
		vertBuffer.rewind();
		normBuffer.rewind();
		faceBuffer.rewind();
		gl.glVertexPointer(3, GL2.GL_FLOAT, 0, vertBuffer);
		gl.glNormalPointer(GL2.GL_FLOAT, 0, normBuffer);
		
		gl.glDrawElements(GL2.GL_QUADS, faces.size(), GL2.GL_UNSIGNED_INT, faceBuffer);
		
		gl.glDisableClientState(GL2.GL_VERTEX_ARRAY);
		gl.glDisableClientState(GL2.GL_NORMAL_ARRAY);
	}
	
	/* computes optimal transformation parameters for OpenGL rendering.
	 * these parameters will place the object at the center of the screen,
	 * and zoom out just enough so that the entire object is visible in the window
	 */	
	void initViewParameters()
	{
		roth = rotv = 0;

		float ball_r = (float) Math.sqrt((xmax-xmin)*(xmax-xmin)
							+ (ymax-ymin)*(ymax-ymin)
							+ (zmax-zmin)*(zmax-zmin)) * 0.707f;

		centerx = (xmax+xmin)/2.f;
		centery = (ymax+ymin)/2.f;
		centerz = (zmax+zmin)/2.f;
		xpos = centerx;
		ypos = centery;
		zpos = ball_r/(float) Math.sin(30.f*Math.PI/180.f)+centerz;

		znear = 0.02f;
		zfar  = zpos - centerz + 3.f * ball_r;

		motionSpeed = 0.002f * ball_r;
		rotateSpeed = 0.1f;

	}	
	
	// these event functions are not used for this assignment
        public void dispose(GLAutoDrawable glautodrawable) { }            
	public void displayChanged(GLAutoDrawable drawable, boolean modeChanged, boolean deviceChanged) { }
	public void keyTyped(KeyEvent e) { }
	public void keyReleased(KeyEvent e) { }
	public void mouseMoved(MouseEvent e) { }
	public void actionPerformed(ActionEvent e) { }
	public void mouseClicked(MouseEvent e) { }
	public void mouseEntered(MouseEvent e) { }
	public void mouseExited(MouseEvent e) {	}	
}
