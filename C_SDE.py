import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog, simpledialog
import re
import json
import datetime
import sys
from typing import List, Dict, Any, Tuple, Set
from collections import defaultdict
import networkx as nx
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.patches import FancyBboxPatch
from matplotlib.lines import Line2D

class CSyntaxDirectedEnvironment:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("C Dataflow Analysis Environment with TTA Blocks")
        self.root.geometry("1400x900")
        self.root.minsize(1200, 700)  # Set minimum window size to ensure buttons stay visible
        
        # Initialize analysis data first
        self.syntax_errors = []
        self.current_analysis = {}
        self.dataflow_analyzer = None
        self.tta_analyzer = None  # NEW: TTA Graph analyzer
        self.current_canvas = None  # For matplotlib cleanup
        
        # C language constructs - define these BEFORE setup_ui()
        self.c_keywords = {
            'auto', 'break', 'case', 'char', 'const', 'continue', 'default', 'do',
            'double', 'else', 'enum', 'extern', 'float', 'for', 'goto', 'if',
            'inline', 'int', 'long', 'register', 'restrict', 'return', 'short',
            'signed', 'sizeof', 'static', 'struct', 'switch', 'typedef', 'union',
            'unsigned', 'void', 'volatile', 'while', '_Bool', '_Complex', '_Imaginary'
        }
        
        self.c_operators = {
            # Arithmetic
            '+', '-', '*', '/', '%', '++', '--',
            # Assignment
            '=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=',
            # Comparison
            '==', '!=', '<', '>', '<=', '>=',
            # Logical
            '&&', '||', '!',
            # Bitwise
            '&', '|', '^', '~', '<<', '>>',
            # Other
            '->', '.', '?', ':'
        }
        
        self.file_io_functions = {
            'fopen', 'fclose', 'fread', 'fwrite', 'fprintf', 'fscanf', 'fgetc', 
            'fputc', 'fgets', 'fputs', 'fseek', 'ftell', 'rewind', 'fflush',
            'printf', 'scanf', 'getchar', 'putchar', 'gets', 'puts'
        }
        
        self.memory_functions = {
            'malloc', 'calloc', 'realloc', 'free', 'memset', 'memcpy', 'memmove', 'memcmp'
        }
        
        self.math_functions = {
            'sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'atan2', 'sinh', 'cosh', 'tanh',
            'exp', 'log', 'log10', 'pow', 'sqrt', 'ceil', 'floor', 'fabs', 'fmod'
        }
        
        # Set up proper closing protocol
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # Now setup UI after all attributes are defined
        self.setup_ui()
        
    def setup_ui(self):
        # Create main frame
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Create paned window for split layout
        paned = ttk.PanedWindow(main_frame, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True, side=tk.TOP, pady=(0, 5))  # Add padding before controls
        
        # Left panel - Code editor
        left_frame = ttk.Frame(paned)
        paned.add(left_frame, weight=2)
        
        # Code editor with line numbers
        editor_frame = ttk.Frame(left_frame)
        editor_frame.pack(fill=tk.BOTH, expand=True)
        
        ttk.Label(editor_frame, text="C Code Editor - Dataflow & TTA Block Analysis", font=('Arial', 12, 'bold')).pack(anchor=tk.W)
        
        # Frame for line numbers and text editor
        text_frame = ttk.Frame(editor_frame)
        text_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Line numbers widget
        self.line_numbers = tk.Text(
            text_frame,
            width=4,
            padx=3,
            takefocus=0,
            fg='gray',
            bg='#2d2d2d',
            font=('Consolas', 11),
            state='disabled'
        )
        self.line_numbers.pack(side=tk.LEFT, fill=tk.Y)
        
        # Text editor
        self.text_editor = scrolledtext.ScrolledText(
            text_frame, 
            wrap=tk.NONE,
            font=('Consolas', 11),
            bg='#1e1e1e',
            fg='#dcdcdc',
            insertbackground='white',
            selectbackground='#404040'
        )
        self.text_editor.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # Synchronize scrolling between line numbers and text editor
        self.text_editor.config(yscrollcommand=self._on_text_scroll)
        self.line_numbers.config(yscrollcommand=self._on_line_scroll)
        
        # Bind events for real-time analysis
        self.text_editor.bind('<KeyRelease>', self.on_text_change)
        self.text_editor.bind('<Button-1>', self.on_text_change)
        self.text_editor.bind('<KeyPress>', self.on_text_change)
        self.text_editor.bind('<MouseWheel>', self._on_mousewheel)
        self.text_editor.bind('<Button-4>', self._on_mousewheel)
        self.text_editor.bind('<Button-5>', self._on_mousewheel)
        
        # Right panel - Analysis results
        right_frame = ttk.Frame(paned)
        paned.add(right_frame, weight=1)
        
        # Analysis notebook
        self.notebook = ttk.Notebook(right_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        
        # Variable Tracking tab
        self.var_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.var_frame, text="Variable Tracking")
        
        ttk.Label(self.var_frame, text="Definition-Use Analysis", font=('Arial', 10, 'bold')).pack(anchor=tk.W)
        self.var_tree = ttk.Treeview(self.var_frame, columns=('Type', 'Line', 'Details'), show='tree headings')
        self.var_tree.heading('#0', text='Variable')
        self.var_tree.heading('Type', text='Type')
        self.var_tree.heading('Line', text='Line')
        self.var_tree.heading('Details', text='Details')
        self.var_tree.column('#0', width=120)
        self.var_tree.column('Type', width=80)
        self.var_tree.column('Line', width=60)
        self.var_tree.column('Details', width=200)
        self.var_tree.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Dataflow Dependencies tab
        self.deps_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.deps_frame, text="Dependencies")
        
        ttk.Label(self.deps_frame, text="Variable Dependencies & Line Analysis", font=('Arial', 10, 'bold')).pack(anchor=tk.W)
        self.deps_text = scrolledtext.ScrolledText(
            self.deps_frame,
            height=8,
            font=('Consolas', 9),
            bg='#f0fff0'
        )
        self.deps_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # TTA Blocks tab (NEW)
        self.tta_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.tta_frame, text="TTA Blocks")
        
        ttk.Label(self.tta_frame, text="Control Flow Blocks & Arcs", font=('Arial', 10, 'bold')).pack(anchor=tk.W)
        self.tta_text = scrolledtext.ScrolledText(
            self.tta_frame,
            height=8,
            font=('Consolas', 9),
            bg='#fff8f0'
        )
        self.tta_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Dependency Graph tab
        self.graph_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.graph_frame, text="Dependency Graph")
        
        ttk.Label(self.graph_frame, text="Visual Dependency Graph", font=('Arial', 10, 'bold')).pack(anchor=tk.W)
        
        # Graph controls
        graph_controls = ttk.Frame(self.graph_frame)
        graph_controls.pack(fill=tk.X, pady=(5, 0))
        ttk.Button(graph_controls, text="Generate Graph", command=self.generate_dependency_graph).pack(side=tk.LEFT)
        ttk.Button(graph_controls, text="Save Graph", command=self.save_dependency_graph).pack(side=tk.LEFT, padx=(5, 0))
        
        # Graph canvas frame
        self.graph_canvas_frame = ttk.Frame(self.graph_frame)
        self.graph_canvas_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # TTA Graph tab (NEW) - with size constraints
        self.tta_graph_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.tta_graph_frame, text="TTA Graph")
        
        ttk.Label(self.tta_graph_frame, text="Control Flow Block Graph", font=('Arial', 10, 'bold')).pack(anchor=tk.W, pady=(5,0))
        
        # TTA Graph controls
        tta_graph_controls = ttk.Frame(self.tta_graph_frame)
        tta_graph_controls.pack(fill=tk.X, pady=(5, 0))
        ttk.Button(tta_graph_controls, text="Generate TTA Graph", command=self.generate_tta_graph).pack(side=tk.LEFT)
        ttk.Button(tta_graph_controls, text="Save TTA Graph", command=self.save_tta_graph).pack(side=tk.LEFT, padx=(5, 0))
        
        # TTA Graph canvas frame with constrained size
        self.tta_graph_canvas_frame = ttk.Frame(self.tta_graph_frame)
        self.tta_graph_canvas_frame.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        self.tta_graph_canvas_frame.pack_propagate(True)  # Allow proper sizing
        
        # C Linked List tab
        self.linked_list_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.linked_list_frame, text="C Linked List")
        
        ttk.Label(self.linked_list_frame, text="Operation Sequence (WRITE/READ/KILL)", font=('Arial', 10, 'bold')).pack(anchor=tk.W)
        self.linked_list_text = scrolledtext.ScrolledText(
            self.linked_list_frame,
            height=8,
            font=('Consolas', 9),
            bg='#f0f8ff'
        )
        self.linked_list_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Syntax errors tab
        self.error_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.error_frame, text="Syntax Check")
        
        ttk.Label(self.error_frame, text="Syntax Analysis", font=('Arial', 10, 'bold')).pack(anchor=tk.W)
        self.error_text = scrolledtext.ScrolledText(
            self.error_frame, 
            height=8,
            font=('Consolas', 9),
            bg='#fff5f5',
            fg='#d00000'
        )
        self.error_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Bottom status bar - pack FIRST to ensure it's at the very bottom
        self.status_bar = ttk.Label(main_frame, text="Ready", relief=tk.SUNKEN)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X, pady=(2, 0))
        
        # Bottom controls frame - pack SECOND so it's above status bar
        controls_frame = ttk.Frame(main_frame)
        controls_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(5, 2))
        
        # Export buttons
        ttk.Button(
            controls_frame, 
            text="Export Dataflow Analysis", 
            command=self.export_analysis
        ).pack(side=tk.LEFT)
        
        # Export C Linked List button
        ttk.Button(
            controls_frame, 
            text="Export C Linked List", 
            command=self.export_c_style_analysis
        ).pack(side=tk.LEFT, padx=(10, 0))
        
        # NEW: Export TTA Graph button
        ttk.Button(
            controls_frame, 
            text="Export TTA Graph", 
            command=self.export_tta_analysis
        ).pack(side=tk.LEFT, padx=(10, 0))
        
        # Load file button
        ttk.Button(
            controls_frame, 
            text="Load C File", 
            command=self.load_file
        ).pack(side=tk.LEFT, padx=(10, 0))
        
        # Save file button
        ttk.Button(
            controls_frame, 
            text="Save C File", 
            command=self.save_file
        ).pack(side=tk.LEFT, padx=(10, 0))
        
        # Analysis refresh button
        ttk.Button(
            controls_frame, 
            text="Refresh Analysis", 
            command=self.analyze_code
        ).pack(side=tk.LEFT, padx=(10, 0))
        
        # Configure syntax highlighting tags
        self.setup_syntax_highlighting()
        
        sample_code = '''#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int main() {
    // Step 1: Initialize variables
    int a = 10;           
    int b = 5;            
    
    // Step 2: Conditional logic
    if (a > b) {
        int sum = a + b;      
        printf("Sum: %d\\n", sum);
    } else {
        int diff = a - b;
        printf("Diff: %d\\n", diff);
    }
    
    // Step 3: Loop structure
    for (int i = 0; i < 3; i++) {
        printf("Loop %d\\n", i);
        int temp = a * i;
        if (temp > 10) {
            break;
        }
    }
    
    // Step 4: Memory operations
    int* ptr = malloc(sizeof(int));   
    if (ptr != NULL) {                
        *ptr = a + b;                
        printf("Ptr value: %d\\n", *ptr);  
        free(ptr);                    
    }
    
    return 0;  
}'''
        self.text_editor.insert('1.0', sample_code)
        self.update_line_numbers()
        self.analyze_code()
    
    def _on_text_scroll(self, *args):
        """Synchronize line numbers with text editor scrolling"""
        self.line_numbers.yview_moveto(args[0])
        return 'break'
    
    def _on_line_scroll(self, *args):
        """Synchronize text editor with line numbers scrolling"""
        self.text_editor.yview_moveto(args[0])
        return 'break'
    
    def _on_mousewheel(self, event):
        """Handle mousewheel scrolling for both widgets"""
        # Scroll both widgets together
        if event.delta:
            delta = -1 * (event.delta / 120)
        else:
            if event.num == 4:
                delta = -1
            else:
                delta = 1
        
        self.text_editor.yview_scroll(int(delta), "units")
        self.line_numbers.yview_scroll(int(delta), "units")
        return 'break'
    
    def update_line_numbers(self):
        """Update line numbers based on text content"""
        self.line_numbers.config(state='normal')
        self.line_numbers.delete('1.0', tk.END)
        
        line_count = self.text_editor.get('1.0', tk.END).count('\n')
        line_numbers = '\n'.join(str(i) for i in range(1, line_count + 1))
        self.line_numbers.insert('1.0', line_numbers)
        
        self.line_numbers.config(state='disabled')
    
    def setup_syntax_highlighting(self):
        """Configure text tags for syntax highlighting"""
        self.text_editor.tag_configure('keyword', foreground='#569cd6')
        self.text_editor.tag_configure('string', foreground='#ce9178')
        self.text_editor.tag_configure('comment', foreground='#6a9955')
        self.text_editor.tag_configure('function', foreground='#dcdcaa')
        self.text_editor.tag_configure('type', foreground='#4ec9b0')
        self.text_editor.tag_configure('number', foreground='#b5cea8')
        self.text_editor.tag_configure('preprocessor', foreground='#c586c0')
        self.text_editor.tag_configure('operator', foreground='#d4d4d4')
        self.text_editor.tag_configure('error', background='#ff4444', foreground='white')
        self.text_editor.tag_configure('definition', background='#2d4a2d', foreground='#90EE90')
        self.text_editor.tag_configure('use', background='#4a4a2d', foreground='#FFD700')
        # NEW: Block highlighting
        self.text_editor.tag_configure('block_start', background='#4a2d4a', foreground='#FFB6C1')
        self.text_editor.tag_configure('block_end', background='#2d4a4a', foreground='#B0E0E6')
    
    def on_text_change(self, event=None):
        """Handle text changes for real-time analysis"""
        # Update line numbers
        self.update_line_numbers()
        
        # Cancel any pending analysis
        if hasattr(self, '_analysis_job'):
            self.root.after_cancel(self._analysis_job)
        # Schedule new analysis
        self._analysis_job = self.root.after(1000, self.analyze_code)  # Debounce analysis
    
    def analyze_code(self):
        """Main analysis function with dataflow and TTA analysis"""
        code = self.text_editor.get('1.0', tk.END)
        
        # Clear previous highlighting
        for tag in ['keyword', 'string', 'comment', 'function', 'type', 'number', 
                   'preprocessor', 'operator', 'error', 'definition', 'use', 'block_start', 'block_end']:
            self.text_editor.tag_remove(tag, '1.0', tk.END)
        
        # Perform syntax highlighting
        self.highlight_syntax(code)
        
        # Perform comprehensive dataflow analysis
        self.dataflow_analyzer = DataflowAnalyzer(code)
        self.dataflow_analyzer.analyze()
        
        # NEW: Perform TTA block analysis
        self.tta_analyzer = TTAGraphAnalyzer(code, self.dataflow_analyzer)
        self.tta_analyzer.analyze()
        
        # Update all analysis displays
        self.update_variable_tracking()
        self.update_dependencies_display()
        self.update_linked_list_display()
        self.update_tta_blocks_display()  # NEW
        self.highlight_definitions_and_uses()
        self.highlight_block_boundaries()  # NEW
        
        # Check for syntax errors
        self.check_syntax_errors(code)
        
        # Update status
        line_count = len(code.splitlines())
        char_count = len(code)
        var_count = len(self.dataflow_analyzer.variables) if self.dataflow_analyzer else 0
        deps_count = len(self.dataflow_analyzer.dependencies) if self.dataflow_analyzer else 0
        block_count = len(self.tta_analyzer.blocks) if self.tta_analyzer else 0
        self.status_bar.config(text=f"Lines: {line_count} | Variables: {var_count} | Dependencies: {deps_count} | Blocks: {block_count}")
    
    def highlight_syntax(self, code):
        """Syntax highlighting for C code"""
        lines = code.splitlines()
        
        for i, line in enumerate(lines):
            # Highlight preprocessor directives
            if line.strip().startswith('#'):
                start = f"{i+1}.0"
                end = f"{i+1}.end"
                self.text_editor.tag_add('preprocessor', start, end)
                continue
            
            # Highlight keywords
            for keyword in self.c_keywords:
                pattern = r'\b' + re.escape(keyword) + r'\b'
                for match in re.finditer(pattern, line):
                    start = f"{i+1}.{match.start()}"
                    end = f"{i+1}.{match.end()}"
                    self.text_editor.tag_add('keyword', start, end)
            
            # Highlight strings
            for match in re.finditer(r'"([^"\\]|\\.)*"', line):
                start = f"{i+1}.{match.start()}"
                end = f"{i+1}.{match.end()}"
                self.text_editor.tag_add('string', start, end)
            
            # Highlight character literals
            for match in re.finditer(r"'([^'\\]|\\.)'", line):
                start = f"{i+1}.{match.start()}"
                end = f"{i+1}.{match.end()}"
                self.text_editor.tag_add('string', start, end)
            
            # Highlight comments
            comment_pos = line.find('//')
            if comment_pos != -1:
                start = f"{i+1}.{comment_pos}"
                end = f"{i+1}.end"
                self.text_editor.tag_add('comment', start, end)
            
            # Highlight numbers
            for match in re.finditer(r'\b\d+\.?\d*[fFlL]?\b', line):
                start = f"{i+1}.{match.start()}"
                end = f"{i+1}.{match.end()}"
                self.text_editor.tag_add('number', start, end)
            
            # Highlight function calls
            for match in re.finditer(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\(', line):
                start = f"{i+1}.{match.start()}"
                end = f"{i+1}.{match.start() + len(match.group(1))}"
                self.text_editor.tag_add('function', start, end)
    
    def update_variable_tracking(self):
        """Update the variable tracking display"""
        # Clear previous data
        for item in self.var_tree.get_children():
            self.var_tree.delete(item)
        
        if not self.dataflow_analyzer:
            return
        
        # Group by variable name
        for var_name, var_info in self.dataflow_analyzer.variables.items():
            # Special display for pointer dereferences
            if var_name.startswith('*'):
                display_name = f"{var_name} (pointer deref)"
                var_type = 'Ptr Deref'
            else:
                display_name = var_name
                var_type = 'Variable'
                
            var_node = self.var_tree.insert('', 'end', text=display_name, values=(var_type, '', ''))
            
            # Add definitions
            if var_info['definitions']:
                def_node = self.var_tree.insert(var_node, 'end', text='Definitions', values=('', '', ''))
                for line_num, details in var_info['definitions']:
                    self.var_tree.insert(def_node, 'end', text=f"Line {line_num}", 
                                       values=('DEF', line_num, details))
            
            # Add uses
            if var_info['uses']:
                use_node = self.var_tree.insert(var_node, 'end', text='Uses', values=('', '', ''))
                for line_num, details in var_info['uses']:
                    self.var_tree.insert(use_node, 'end', text=f"Line {line_num}", 
                                       values=('USE', line_num, details))
    
    def update_dependencies_display(self):
        """Update the dependencies display"""
        self.deps_text.delete('1.0', tk.END)
        
        if not self.dataflow_analyzer:
            return
        
        deps_output = []
        deps_output.append("=== VARIABLE DEPENDENCIES ===\n")
        
        # Variable dependencies
        deps_output.append("Variable Dependencies:")
        for var, deps in self.dataflow_analyzer.dependencies.items():
            if deps:
                if var.startswith('*'):
                    deps_output.append(f"  {var} (pointer dereference) depends on: {', '.join(deps)}")
                else:
                    deps_output.append(f"  {var} depends on: {', '.join(deps)}")
            else:
                deps_output.append(f"  {var} has no dependencies")
        
        deps_output.append("\n=== LINE-BY-LINE DATAFLOW ANALYSIS ===")
        for line_num in sorted(self.dataflow_analyzer.line_analysis.keys()):
            analysis = self.dataflow_analyzer.line_analysis[line_num]
            deps_output.append(f"\nLine {line_num}:")
            if analysis['reads']:
                deps_output.append(f"  READS: {', '.join(analysis['reads'])}")
            if analysis['writes']:
                deps_output.append(f"  WRITES: {', '.join(analysis['writes'])}")
            if analysis['operation']:
                deps_output.append(f"  OPERATION: {analysis['operation']}")
        
        deps_output.append("\n=== REACHING DEFINITIONS ===")
        for line_num in sorted(self.dataflow_analyzer.reaching_definitions.keys()):
            reaching = self.dataflow_analyzer.reaching_definitions[line_num]
            if reaching:
                deps_output.append(f"Line {line_num} uses definitions from: {', '.join(reaching)}")
        
        self.deps_text.insert('1.0', '\n'.join(deps_output))
    
    def update_linked_list_display(self):
        """Update the C linked list operation sequence display"""
        self.linked_list_text.delete('1.0', tk.END)
        
        if not self.dataflow_analyzer:
            return
        
        operations = self.dataflow_analyzer.build_operation_sequence()
        
        output = []
        output.append("=== C LINKED LIST OPERATION SEQUENCE ===\n")
        output.append("Operation Types: WRITE (define), READ (use), KILL (destroy/redefine)")
        output.append(f"Total Operations: {len(operations)}")
        output.append("List Head: " + (str(operations[0]['operation_id']) if operations else "NULL"))
        output.append("\n" + "="*60)
        
        for i, op in enumerate(operations):
            next_ptr = f"&node_{op['next']}" if op['next'] is not None else "NULL"
            output.append(f"\nNode {i} (ID: {op['operation_id']}):")
            output.append(f"  Variable: {op['variable_name']}")
            output.append(f"  Operation: {op['operation']}")
            output.append(f"  Line: {op['line_number']}")
            output.append(f"  Details: {op['details']}")
            output.append(f"  Next: {next_ptr}")
        
        output.append("\n" + "="*60)
        output.append("C Structure Definition:")
        output.append("typedef enum { WRITE, READ, KILL } operation_types;")
        output.append("struct operation_element {")
        output.append("    int operation_id;")
        output.append("    char* variable_name;") 
        output.append("    operation_types operation;")
        output.append("    int line_number;")
        output.append("    char* details;")
        output.append("    struct operation_element* next;")
        output.append("};")
        
        self.linked_list_text.insert('1.0', '\n'.join(output))
    
    def update_tta_blocks_display(self):
        """Update the TTA blocks display"""
        self.tta_text.delete('1.0', tk.END)
        
        if not self.tta_analyzer:
            return
        
        output = []
        output.append("=== TTA GRAPH BLOCKS & ARCS ===\n")
        output.append(f"Total Blocks: {len(self.tta_analyzer.blocks)}")
        output.append(f"Total Arcs: {len(self.tta_analyzer.arcs)}")
        output.append("\n" + "="*60)
        
        # Display blocks
        output.append("\n📦 BLOCKS:")
        for i, block in enumerate(self.tta_analyzer.blocks):
            output.append(f"\nBlock {i} (Type: {block['node_type']}):")
            output.append(f"  Lines: {block['start_line']}-{block['end_line']}")
            output.append(f"  Code Preview: {block['code_preview']}")
            if block['operation_sequence']:
                output.append(f"  Operations: {len(block['operation_sequence'])} ops")
        
        # Display arcs
        output.append(f"\n🔗 ARCS:")
        for arc in self.tta_analyzer.arcs:
            arc_type = arc['arc_type']
            symbol = "→" if arc_type == "solid" else ("--→" if arc_type == "dashed" else "⋯→")
            output.append(f"  Block{arc['from']} {symbol} Block{arc['to']} ({arc_type}: {arc['description']})")
        
        output.append("\n" + "="*60)
        output.append("Node Types: START, END, ACTIVITY, XOR, LOOP, BLOCK")
        output.append("Arc Types: solid (sequential), dashed (conditional), dotted (loop back)")
        
        self.tta_text.insert('1.0', '\n'.join(output))
    
    def highlight_definitions_and_uses(self):
        """Highlight variable definitions and uses in the editor"""
        if not self.dataflow_analyzer:
            return
        
        # Highlight definitions
        for var_name, var_info in self.dataflow_analyzer.variables.items():
            for line_num, details in var_info['definitions']:
                line_start = f"{line_num}.0"
                line_end = f"{line_num}.end"
                line_content = self.text_editor.get(line_start, line_end)
                
                # Skip if this line is a comment
                if line_content.strip().startswith('//'):
                    continue
                
                # Find the variable name in the line but skip comments
                comment_pos = line_content.find('//')
                search_area = line_content[:comment_pos] if comment_pos != -1 else line_content
                
                var_pos = search_area.find(var_name)
                if var_pos != -1:
                    # Check if it's a whole word
                    if ((var_pos == 0 or not search_area[var_pos-1].isalnum() and search_area[var_pos-1] != '_') and 
                        (var_pos + len(var_name) >= len(search_area) or 
                         not search_area[var_pos + len(var_name)].isalnum() and search_area[var_pos + len(var_name)] != '_')):
                        start = f"{line_num}.{var_pos}"
                        end = f"{line_num}.{var_pos + len(var_name)}"
                        self.text_editor.tag_add('definition', start, end)
            
            # Highlight uses
            for line_num, details in var_info['uses']:
                line_start = f"{line_num}.0"
                line_end = f"{line_num}.end"
                line_content = self.text_editor.get(line_start, line_end)
                
                # Skip if this line is a comment
                if line_content.strip().startswith('//'):
                    continue
                
                # Find variables only before any comment
                comment_pos = line_content.find('//')
                search_area = line_content[:comment_pos] if comment_pos != -1 else line_content
                
                # Find all occurrences of the variable in the non-comment part
                pos = 0
                while True:
                    var_pos = search_area.find(var_name, pos)
                    if var_pos == -1:
                        break
                    # Check if it's a whole word (not part of another identifier)
                    if ((var_pos == 0 or not search_area[var_pos-1].isalnum() and search_area[var_pos-1] != '_') and 
                        (var_pos + len(var_name) >= len(search_area) or 
                         not search_area[var_pos + len(var_name)].isalnum() and search_area[var_pos + len(var_name)] != '_')):
                        start = f"{line_num}.{var_pos}"
                        end = f"{line_num}.{var_pos + len(var_name)}"
                        self.text_editor.tag_add('use', start, end)
                    pos = var_pos + 1
    
    def highlight_block_boundaries(self):
        """Highlight TTA block boundaries in the editor"""
        if not self.tta_analyzer:
            return
        
        for block in self.tta_analyzer.blocks:
            # Highlight block start
            start_line = block['start_line']
            start_pos = f"{start_line}.0"
            start_end = f"{start_line}.end"
            self.text_editor.tag_add('block_start', start_pos, start_end)
            
            # Highlight block end if different from start
            end_line = block['end_line']
            if end_line != start_line:
                end_pos = f"{end_line}.0"
                end_end = f"{end_line}.end"
                self.text_editor.tag_add('block_end', end_pos, end_end)
    
    def generate_dependency_graph(self):
        """Generate and display dependency graph"""
        if not self.dataflow_analyzer:
            messagebox.showerror("Error", "No dataflow analysis available")
            return
        
        # Clear existing graph
        for widget in self.graph_canvas_frame.winfo_children():
            widget.destroy()
        
        try:
            # Close any existing matplotlib figures
            plt.close('all')
            
            # Create networkx graph
            G = nx.DiGraph()
            
            # Add nodes and edges based on dependencies
            for var, deps in self.dataflow_analyzer.dependencies.items():
                G.add_node(var)
                for dep in deps:
                    G.add_edge(dep, var)
            
            # Create matplotlib figure
            fig, ax = plt.subplots(figsize=(10, 6))
            fig.patch.set_facecolor('white')
            
            if G.nodes():
                pos = nx.spring_layout(G, k=2, iterations=50)
                
                # Different colors for pointer dereferences
                node_colors = []
                for node in G.nodes():
                    if node.startswith('*'):
                        node_colors.append('lightcoral')  # Pointer dereferences in light red
                    else:
                        node_colors.append('lightblue')   # Regular variables in light blue
                
                # Draw the graph
                nx.draw_networkx_nodes(G, pos, node_color=node_colors, 
                                     node_size=1500, alpha=0.8, ax=ax)
                nx.draw_networkx_labels(G, pos, font_size=10, font_weight='bold', ax=ax)
                nx.draw_networkx_edges(G, pos, edge_color='gray', 
                                     arrows=True, arrowsize=20, ax=ax)
                
                ax.set_title("Variable Dependency Graph\n(Blue: variables, Red: pointer dereferences)", 
                           fontsize=12, fontweight='bold')
            else:
                ax.text(0.5, 0.5, 'No dependencies found', 
                       horizontalalignment='center', verticalalignment='center',
                       transform=ax.transAxes, fontsize=14)
                ax.set_title("Variable Dependency Graph", fontsize=12, fontweight='bold')
            
            ax.axis('off')
            plt.tight_layout()
            
            # Embed in tkinter
            canvas = FigureCanvasTkAgg(fig, self.graph_canvas_frame)
            canvas.draw()
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            
            # Store canvas reference for cleanup
            self.current_canvas = canvas
            
        except Exception as e:
            messagebox.showerror("Graph Error", f"Could not generate graph: {str(e)}")
    
    def generate_tta_graph(self):
        """Generate and display TTA block graph with improved spacing and visibility"""
        if not self.tta_analyzer:
            messagebox.showerror("Error", "No TTA analysis available")
            return
        
        # Clear existing graph
        for widget in self.tta_graph_canvas_frame.winfo_children():
            widget.destroy()
        
        try:
            # Close any existing matplotlib figures
            plt.close('all')
            
            # Calculate figure size based on number of blocks
            num_blocks = len(self.tta_analyzer.blocks)
            fig_height = max(12, num_blocks * 0.8)  # Scale height with number of blocks
            fig_width = max(16, 16 + (num_blocks - 20) * 0.2) if num_blocks > 20 else 16
            
            # Create matplotlib figure with dynamic size
            fig, ax = plt.subplots(figsize=(fig_width, fig_height))
            fig.patch.set_facecolor('white')
            
            if self.tta_analyzer.blocks:
                # Check for extremely large graphs
                if num_blocks > 100:
                    response = messagebox.askyesno(
                        "Large Graph Warning", 
                        f"This graph has {num_blocks} blocks and may be difficult to view.\n\n"
                        "Would you like to continue? (Consider using 'Save TTA Graph' for better viewing)"
                    )
                    if not response:
                        return
                
                # Create custom hierarchical layout
                pos = self.create_hierarchical_layout()
                
                # Draw nodes with better sizing
                for i, block in enumerate(self.tta_analyzer.blocks):
                    x, y = pos[i]
                    
                    # Adaptive node sizing based on graph complexity
                    if num_blocks <= 20:
                        box_width, box_height = 2.4, 1.0
                        font_size = 10
                    elif num_blocks <= 40:
                        box_width, box_height = 2.8, 1.2
                        font_size = 9
                    else:
                        box_width, box_height = 3.2, 1.4
                        font_size = 8
                    
                    # Color nodes by type
                    if block['node_type'] == 'START':
                        color = 'lightgreen'
                        edge_color = 'darkgreen'
                    elif block['node_type'] == 'END':
                        color = 'lightcoral'
                        edge_color = 'darkred'
                    elif block['node_type'] == 'XOR':
                        color = 'lightyellow'
                        edge_color = 'orange'
                    elif block['node_type'] == 'LOOP':
                        color = 'lightblue'
                        edge_color = 'darkblue'
                    else:  # ACTIVITY, BLOCK
                        color = 'lightgray'
                        edge_color = 'gray'
                    
                    # Draw node as rectangle with rounded corners
                    box = FancyBboxPatch((x-box_width/2, y-box_height/2), box_width, box_height,
                                        boxstyle="round,pad=0.1",
                                        facecolor=color,
                                        edgecolor=edge_color,
                                        linewidth=2,
                                        alpha=0.9,
                                        zorder=2)
                    ax.add_patch(box)
                    
                    # Add label with better formatting - use line numbers only for very large graphs
                    if num_blocks > 50:
                        label = f"{block['node_type'][0]}{block['node_type'][-1]}\n{block['start_line']}-{block['end_line']}"
                    else:
                        label = f"{block['node_type']}\n(L{block['start_line']}-{block['end_line']})"
                    ax.text(x, y, label, ha='center', va='center', fontsize=font_size, 
                           fontweight='bold', zorder=3)
                
                # Draw edges with different styles and curves
                for arc in self.tta_analyzer.arcs:
                    from_pos = pos[arc['from']]
                    to_pos = pos[arc['to']]
                    
                    # Calculate control points for curved arrows
                    dx = to_pos[0] - from_pos[0]
                    dy = to_pos[1] - from_pos[1]
                    
                    # Set edge style and color based on arc type - adjust for graph size
                    if arc['arc_type'] == 'solid':
                        color = 'black'
                        linestyle = '-'
                        linewidth = 2 if num_blocks <= 30 else 1.5
                        connectionstyle = "arc3,rad=0.1"
                    elif arc['arc_type'] == 'dashed':
                        color = 'blue'
                        linestyle = '--'
                        linewidth = 2.5 if num_blocks <= 30 else 2
                        # Curve more for conditional branches
                        if dx != 0:  # Horizontal component
                            connectionstyle = "arc3,rad=0.3"
                        else:
                            connectionstyle = "arc3,rad=0.2"
                    else:  # dotted (loop back)
                        color = 'red'
                        linestyle = ':'
                        linewidth = 3 if num_blocks <= 30 else 2.5
                        # Loop backs need more curve
                        connectionstyle = "arc3,rad=-0.5"  # Negative for opposite curve
                    
                    # Get node dimensions for this block
                    if num_blocks <= 20:
                        box_w, box_h = 2.4, 1.0
                    elif num_blocks <= 40:
                        box_w, box_h = 2.8, 1.2
                    else:
                        box_w, box_h = 3.2, 1.4
                    
                    # Adjust arrow positions to connect to box edges
                    y_offset = box_h / 2
                    x_offset = box_w / 2
                    
                    # Calculate connection points
                    if dy < 0:  # Arrow going down
                        from_y = from_pos[1] - y_offset
                        to_y = to_pos[1] + y_offset
                    else:  # Arrow going up
                        from_y = from_pos[1] + y_offset
                        to_y = to_pos[1] - y_offset
                    
                    if dx > 0:  # Arrow going right
                        from_x = from_pos[0] + x_offset * 0.8
                        to_x = to_pos[0] - x_offset * 0.8
                    elif dx < 0:  # Arrow going left
                        from_x = from_pos[0] - x_offset * 0.8
                        to_x = to_pos[0] + x_offset * 0.8
                    else:  # Vertical arrow
                        from_x = from_pos[0]
                        to_x = to_pos[0]
                    
                    # Draw arrow with curve
                    ax.annotate('', xy=(to_x, to_y), xytext=(from_x, from_y),
                               arrowprops=dict(arrowstyle='->', 
                                             color=color, 
                                             linestyle=linestyle, 
                                             linewidth=linewidth,
                                             connectionstyle=connectionstyle,
                                             shrinkA=5, shrinkB=5),
                               zorder=1)
                
                # Title removed to prevent cutoff
                # ax.set_title("TTA Control Flow Graph\n(Improved Spacing and Visibility)", 
                #            fontsize=18, fontweight='bold', pad=20)
                
                # Add legend with better positioning - at the bottom where there's space
                legend_elements = [
                    Line2D([0], [0], color='black', lw=2, label='Sequential (→)'),
                    Line2D([0], [0], color='blue', lw=2.5, linestyle='--', label='Conditional (--→)'),
                    Line2D([0], [0], color='red', lw=3, linestyle=':', label='Loop Back (⋯→)')
                ]
                # Place legend at the bottom of the graph
                ax.legend(handles=legend_elements, 
                         loc='lower center', 
                         bbox_to_anchor=(0.5, -0.1),
                         ncol=3,  # Horizontal layout
                         fontsize=11, 
                         framealpha=0.9,
                         borderaxespad=0)
                
                # Set axis limits with padding (more padding for large graphs)
                all_x = [p[0] for p in pos.values()]
                all_y = [p[1] for p in pos.values()]
                
                x_padding = 3 if num_blocks > 30 else 2
                y_padding = 2 if num_blocks > 30 else 1.5
                
                x_min, x_max = min(all_x) - x_padding, max(all_x) + x_padding
                y_min, y_max = min(all_y) - y_padding, max(all_y) + y_padding
                
                ax.set_xlim(x_min, x_max)
                ax.set_ylim(y_min, y_max)
                
                # Add grid for better visibility (less prominent for large graphs)
                grid_alpha = 0.1 if num_blocks > 30 else 0.2
                ax.grid(True, alpha=grid_alpha, linestyle='--')
                
            else:
                ax.text(0.5, 0.5, 'No blocks found', 
                       horizontalalignment='center', verticalalignment='center',
                       transform=ax.transAxes, fontsize=14)
            
            # Adjust aspect ratio for very tall graphs
            if num_blocks > 40:
                ax.set_aspect('auto')  # Allow stretching for better visibility
            else:
                ax.set_aspect('equal')
            ax.axis('off')
            plt.tight_layout(rect=[0, 0.05, 1, 0.98])  # Adjusted spacing without title
            
            # Embed in tkinter with size constraints
            canvas = FigureCanvasTkAgg(fig, self.tta_graph_canvas_frame)
            canvas.draw()
            
            # Get the canvas widget and limit its size
            canvas_widget = canvas.get_tk_widget()
            
            # Set maximum display size to prevent UI issues
            max_height = 600  # Maximum height in pixels
            if fig_height > 10:  # If figure is very tall
                canvas_widget.config(height=max_height)
            
            canvas_widget.pack(fill=tk.BOTH, expand=True)
            
            # Store canvas reference for cleanup
            self.current_canvas = canvas
            
        except Exception as e:
            messagebox.showerror("TTA Graph Error", f"Could not generate TTA graph: {str(e)}")
    
    def create_hierarchical_layout(self):
        """Create a clean hierarchical layout for TTA blocks with better spacing"""
        pos = {}
        
        # Calculate dynamic spacing based on number of blocks
        num_blocks = len(self.tta_analyzer.blocks)
        
        # Adaptive spacing parameters
        if num_blocks <= 15:
            x_center = 6
            x_branch_offset = 4
            y_spacing = 2.5
        elif num_blocks <= 30:
            x_center = 8
            x_branch_offset = 5
            y_spacing = 3.5
        else:
            x_center = 10
            x_branch_offset = 6
            y_spacing = 4.5
        
        # Extra spacing for readability
        y_branch_extra = y_spacing * 0.6
        
        # Start from top with dynamic spacing
        y_level = num_blocks * y_spacing * 1.2  # Extra margin at top
        
        # Track which blocks we've positioned
        positioned = set()
        
        # First pass: identify all XOR blocks and their branches
        xor_blocks = []
        for i, block in enumerate(self.tta_analyzer.blocks):
            if block['node_type'] == 'XOR':
                branches = self._find_xor_branches(i)
                xor_blocks.append((i, branches))
        
        # Position blocks level by level
        for i, block in enumerate(self.tta_analyzer.blocks):
            if i in positioned:
                continue
                
            block_type = block['node_type']
            
            if block_type == 'START':
                # START at the very top center
                pos[i] = (x_center, y_level)
                y_level -= y_spacing
                positioned.add(i)
                
            elif block_type == 'LOOP':
                # LOOP blocks get center position with extra space
                pos[i] = (x_center, y_level)
                y_level -= y_spacing
                positioned.add(i)
                
            elif block_type == 'XOR':
                # XOR blocks get center position
                pos[i] = (x_center, y_level)
                
                # Find branches for this XOR
                branches = self._find_xor_branches(i)
                
                # Position branches with more horizontal separation
                branch_y = y_level - y_spacing
                
                if len(branches) >= 1 and branches[0] not in positioned:
                    # True branch to the left
                    pos[branches[0]] = (x_center - x_branch_offset, branch_y)
                    positioned.add(branches[0])
                
                if len(branches) >= 2 and branches[1] not in positioned:
                    # False branch to the right
                    pos[branches[1]] = (x_center + x_branch_offset, branch_y)
                    positioned.add(branches[1])
                
                # Extra space after branches
                y_level -= (y_spacing * 2.5 + y_branch_extra)  # More space after XOR branches
                positioned.add(i)
                
            elif block_type == 'END':
                # END at the bottom with adequate spacing
                pos[i] = (x_center, y_spacing * 2)  # More space from bottom
                positioned.add(i)
                
            else:  # ACTIVITY
                if i not in positioned:
                    # Check if this is a merge point after branches
                    is_merge = False
                    for xor_idx, branches in xor_blocks:
                        if i > max(branches) if branches else xor_idx:
                            is_merge = True
                            break
                    
                    # Add extra space before merge points
                    if is_merge:
                        y_level -= y_spacing * 0.5
                    
                    pos[i] = (x_center, y_level)
                    y_level -= y_spacing
                    positioned.add(i)
        
        return pos
    
    def find_next_block(self, from_block, branch_type):
        """Find the next block for a given branch type"""
        # Access blocks through the TTA analyzer
        if not self.tta_analyzer or from_block >= len(self.tta_analyzer.blocks):
            return None
            
        branches = self.tta_analyzer._find_xor_branches(from_block)
        
        if branch_type == 'true' and branches:
            return branches[0]
        elif branch_type == 'false' and len(branches) > 1:
            return branches[1]
        
        return None
    
    def _find_xor_branches(self, xor_idx):
        """Helper method to find XOR branches - delegates to TTA analyzer"""
        if self.tta_analyzer and xor_idx < len(self.tta_analyzer.blocks):
            return self.tta_analyzer._find_xor_branches(xor_idx)
        return []
    
    def save_dependency_graph(self):
        """Save dependency graph as image"""
        if not self.dataflow_analyzer:
            messagebox.showerror("Error", "No dataflow analysis available")
            return
        
        try:
            filename = filedialog.asksaveasfilename(
                title="Save Dependency Graph",
                initialfile="dependency_graph.png",
                filetypes=[("PNG files", "*.png"), ("PDF files", "*.pdf"), ("All files", "*.*")]
            )
        except Exception as dialog_error:
            print(f"File dialog error: {dialog_error}")
            filename = simpledialog.askstring("Save Graph", "Enter filename (with extension):")
        
        if filename:
            try:
                # Add appropriate extension if missing
                if not any(filename.lower().endswith(ext) for ext in ['.png', '.pdf', '.jpg', '.jpeg']):
                    filename += '.png'
                
                # Create the graph again for saving
                G = nx.DiGraph()
                for var, deps in self.dataflow_analyzer.dependencies.items():
                    G.add_node(var)
                    for dep in deps:
                        G.add_edge(dep, var)
                
                fig = plt.figure(figsize=(12, 8))
                if G.nodes():
                    pos = nx.spring_layout(G, k=2, iterations=50)
                    
                    # Different colors for pointer dereferences
                    node_colors = []
                    for node in G.nodes():
                        if node.startswith('*'):
                            node_colors.append('lightcoral')
                        else:
                            node_colors.append('lightblue')
                    
                    nx.draw_networkx_nodes(G, pos, node_color=node_colors, node_size=2000, alpha=0.8)
                    nx.draw_networkx_labels(G, pos, font_size=12, font_weight='bold')
                    nx.draw_networkx_edges(G, pos, edge_color='gray', arrows=True, arrowsize=25)
                    plt.title("Variable Dependency Graph\n(Blue: variables, Red: pointer dereferences)", fontsize=16, fontweight='bold')
                
                plt.axis('off')
                plt.tight_layout()
                plt.savefig(filename, dpi=300, bbox_inches='tight')
                plt.close(fig)  # Properly close the figure
                
                messagebox.showinfo("Success", f"Graph saved to {filename}")
                
            except Exception as e:
                messagebox.showerror("Save Error", f"Could not save graph: {str(e)}")
    
    def save_tta_graph(self):
        """Save TTA graph as image"""
        if not self.tta_analyzer:
            messagebox.showerror("Error", "No TTA analysis available")
            return
        
        try:
            filename = filedialog.asksaveasfilename(
                title="Save TTA Graph",
                initialfile="tta_graph.png",
                filetypes=[("PNG files", "*.png"), ("PDF files", "*.pdf"), ("All files", "*.*")]
            )
        except Exception as dialog_error:
            print(f"File dialog error: {dialog_error}")
            filename = simpledialog.askstring("Save TTA Graph", "Enter filename (with extension):")
        
        if filename:
            try:
                # Add appropriate extension if missing
                if not any(filename.lower().endswith(ext) for ext in ['.png', '.pdf', '.jpg', '.jpeg']):
                    filename += '.png'
                
                # Regenerate and save the TTA graph
                self.tta_analyzer.save_graph_image(filename)
                messagebox.showinfo("Success", f"TTA Graph saved to {filename}")
                
            except Exception as e:
                messagebox.showerror("Save Error", f"Could not save TTA graph: {str(e)}")
    
    def check_syntax_errors(self, code):
        """Basic syntax error checking for C code"""
        self.syntax_errors = []
        lines = code.splitlines()
        
        # Simple checks
        brace_count = 0
        paren_count = 0
        bracket_count = 0
        
        for i, line in enumerate(lines, 1):
            line_stripped = line.strip()
            
            # Skip comments and preprocessor
            if line_stripped.startswith('//') or line_stripped.startswith('#'):
                continue
            
            # Count braces, parentheses, brackets
            brace_count += line.count('{') - line.count('}')
            paren_count += line.count('(') - line.count(')')
            bracket_count += line.count('[') - line.count(']')
            
            # Check for unterminated strings
            if line.count('"') % 2 != 0:
                self.syntax_errors.append(f"Line {i}: Unterminated string")
        
        # Check unmatched brackets
        if brace_count != 0:
            self.syntax_errors.append(f"Unmatched braces: {abs(brace_count)} extra")
        if paren_count != 0:
            self.syntax_errors.append(f"Unmatched parentheses: {abs(paren_count)} extra")
        if bracket_count != 0:
            self.syntax_errors.append(f"Unmatched brackets: {abs(bracket_count)} extra")
        
        # Display results
        self.error_text.delete('1.0', tk.END)
        if self.syntax_errors:
            self.error_text.insert('1.0', '\n'.join(self.syntax_errors))
        else:
            self.error_text.insert('1.0', "✓ No syntax errors detected!")
    
    def load_file(self):
        """Load a C file"""
        try:
            filename = filedialog.askopenfilename(
                title="Load C File",
                filetypes=[("C files", "*.c"), ("Header files", "*.h"), ("All files", "*.*")]
            )
        except Exception as dialog_error:
            print(f"File dialog error: {dialog_error}")
            filename = simpledialog.askstring("Load File", "Enter filename to load:")
        
        if filename:
            try:
                with open(filename, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                self.text_editor.delete('1.0', tk.END)
                self.text_editor.insert('1.0', content)
                self.update_line_numbers()
                self.analyze_code()
                
                self.status_bar.config(text=f"Loaded: {filename}")
                
            except Exception as e:
                messagebox.showerror("Load Error", f"Failed to load file:\n{str(e)}")
    
    def save_file(self):
        """Save the current code to a C file"""
        try:
            filename = filedialog.asksaveasfilename(
                title="Save C File",
                initialfile="code.c",
                filetypes=[("C files", "*.c"), ("Header files", "*.h"), ("All files", "*.*")]
            )
        except Exception as dialog_error:
            print(f"File dialog error: {dialog_error}")
            filename = simpledialog.askstring("Save File", "Enter filename to save (with .c extension):")
        
        if filename:
            try:
                # Add .c extension if no extension provided
                if not any(filename.lower().endswith(ext) for ext in ['.c', '.h']):
                    filename += '.c'
                
                content = self.text_editor.get('1.0', tk.END)
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(content)
                
                self.status_bar.config(text=f"Saved: {filename}")
                
            except Exception as e:
                messagebox.showerror("Save Error", f"Failed to save file:\n{str(e)}")
    
    def export_analysis(self):
        """Export comprehensive dataflow analysis to JSON"""
        try:
            code = self.text_editor.get('1.0', tk.END)
            
            export_data = {
                "metadata": {
                    "timestamp": datetime.datetime.now().isoformat(),
                    "c_dataflow_version": "2.1",
                    "analysis_type": "comprehensive_dataflow",
                    "code_stats": {
                        "lines": len(code.splitlines()),
                        "characters": len(code),
                        "words": len(code.split())
                    }
                },
                "syntax_errors": self.syntax_errors,
                "dataflow_analysis": {}
            }
            
            if self.dataflow_analyzer:
                export_data["dataflow_analysis"] = {
                    "variables": self.dataflow_analyzer.variables,
                    "dependencies": self.dataflow_analyzer.dependencies,
                    "line_analysis": self.dataflow_analyzer.line_analysis,
                    "reaching_definitions": self.dataflow_analyzer.reaching_definitions
                }
            
            filename = None
            try:
                filename = filedialog.asksaveasfilename(
                    title="Export Dataflow Analysis to JSON",
                    initialfile="dataflow_analysis.json",
                    filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
                )
            except Exception as dialog_error:
                print(f"File dialog error: {dialog_error}")
                filename = simpledialog.askstring("Export Analysis", "Enter filename (with .json extension):")
            
            if filename and not filename.lower().endswith('.json'):
                filename += '.json'
            
            if filename:
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(export_data, f, indent=2, ensure_ascii=False)
                
                messagebox.showinfo("Export Successful", f"Dataflow analysis exported to:\n{filename}")
                self.status_bar.config(text=f"Exported to {filename}")
        
        except Exception as e:
            error_msg = f"Failed to export analysis:\n{str(e)}"
            print(f"Export error details: {e}")
            messagebox.showerror("Export Error", error_msg)
    
    def export_c_style_analysis(self):
        """Export dataflow analysis in C linked list format"""
        if not self.dataflow_analyzer:
            messagebox.showerror("Error", "No dataflow analysis available")
            return
        
        try:
            # Get the C-style linked list format
            c_linked_list_data = self.dataflow_analyzer.export_c_linked_list_format()
            
            # Get filename
            filename = None
            try:
                filename = filedialog.asksaveasfilename(
                    title="Export C-Style Linked List Dataflow",
                    initialfile="c_dataflow_linked_list.json",
                    filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
                )
            except Exception as dialog_error:
                print(f"File dialog error: {dialog_error}")
                filename = simpledialog.askstring("Export C-Style", "Enter filename (with .json extension):")
            
            if filename and not filename.lower().endswith('.json'):
                filename += '.json'
            
            if filename:
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(c_linked_list_data, f, indent=2, ensure_ascii=False)
                
                messagebox.showinfo("Export Successful", f"C-style linked list exported to:\n{filename}")
                self.status_bar.config(text=f"C-style format exported to {filename}")
        
        except Exception as e:
            error_msg = f"Failed to export C-style analysis:\n{str(e)}"
            messagebox.showerror("Export Error", error_msg)
    
    def export_tta_analysis(self):
        """Export TTA graph analysis in JSON format"""
        if not self.tta_analyzer:
            messagebox.showerror("Error", "No TTA analysis available")
            return
        
        try:
            # Get the TTA graph format
            tta_graph_data = self.tta_analyzer.export_tta_graph_format()
            
            # Get filename
            filename = None
            try:
                filename = filedialog.asksaveasfilename(
                    title="Export TTA Graph Analysis",
                    initialfile="tta_graph_analysis.json",
                    filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
                )
            except Exception as dialog_error:
                print(f"File dialog error: {dialog_error}")
                filename = simpledialog.askstring("Export TTA", "Enter filename (with .json extension):")
            
            if filename and not filename.lower().endswith('.json'):
                filename += '.json'
            
            if filename:
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(tta_graph_data, f, indent=2, ensure_ascii=False)
                
                messagebox.showinfo("Export Successful", f"TTA graph exported to:\n{filename}")
                self.status_bar.config(text=f"TTA format exported to {filename}")
        
        except Exception as e:
            error_msg = f"Failed to export TTA analysis:\n{str(e)}"
            messagebox.showerror("Export Error", error_msg)
    
    def run(self):
        """Start the C SDE"""
        self.root.mainloop()
    
    def on_closing(self):
        """Handle proper application closing"""
        try:
            # Clean up matplotlib canvas if it exists
            if hasattr(self, 'current_canvas') and self.current_canvas:
                self.current_canvas.get_tk_widget().destroy()
            
            # Close any matplotlib figures
            plt.close('all')
            
            # Destroy the tkinter window
            self.root.quit()
            self.root.destroy()
            
        except Exception as e:
            print(f"Error during closing: {e}")
        finally:
            # Force exit to ensure command prompt returns
            sys.exit(0)

class DataflowAnalyzer:
    """Comprehensive dataflow analyzer for C code"""
    
    def __init__(self, code):
        self.code = code
        self.lines = code.splitlines()
        
        # Analysis results
        self.variables = {}  # {var_name: {'definitions': [(line, details)], 'uses': [(line, details)]}}
        self.dependencies = {}  # {var: [list of vars it depends on]}
        self.line_analysis = {}  # {line_num: {'reads': [], 'writes': [], 'operation': ''}}
        self.reaching_definitions = {}  # {line_num: [list of lines that can reach this line]}
        
    def analyze(self):
        """Perform comprehensive dataflow analysis"""
        self.analyze_variables()
        self.build_dependencies()
        self.compute_reaching_definitions()
    
    def analyze_variables(self):
        """Analyze variable definitions and uses"""
        for i, line in enumerate(self.lines, 1):
            line_stripped = line.strip()
            
            # Initialize tracking for this line
            reads = []
            writes = []
            operation = ""
            
            # Skip empty lines, comments, and preprocessor
            if not line_stripped or line_stripped.startswith('//') or line_stripped.startswith('#'):
                continue
            
            # Skip function definition lines (they have different scoping rules)
            if re.search(r'\b(int|char|double|float|long|short|void)\s+[a-zA-Z_][a-zA-Z0-9_]*\s*\([^)]*\)\s*{', line):
                operation = "Function definition"
                continue
            
            # IMPORTANT: Check pointer dereference assignments FIRST (*ptr = value)
            if (re.search(r'\*\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*=', line) and 
                not re.search(r'==', line) and 
                not re.search(r'\b(int|char|double|float|long|short|void)\s*\*', line)):
                deref_match = re.search(r'\*\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*=', line)
                if deref_match:
                    ptr_name = deref_match.group(1)
                    deref_name = f"*{ptr_name}"  # Track as pseudo-variable
                    operation = f"Pointer dereference assignment: *{ptr_name} = value"
                    
                    # The pointer itself is USED (read from)
                    reads.append(ptr_name)
                    
                    # Track the dereference as a write
                    writes.append(deref_name)
                    self.add_variable_definition(deref_name, i, operation)
                    
                    # Find what's being assigned to the dereferenced pointer
                    assignment_part = line.split('=', 1)[1] if '=' in line else ""
                    reads.extend(self.extract_variables_from_expression(assignment_part))
            
            # Variable declarations/definitions (including pointer declarations)
            elif re.search(r'\b(int|char|double|float|long|short|void)\s*\*?\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*=', line):
                decl_match = re.search(r'\b(int|char|double|float|long|short|void)\s*\*?\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*=', line)
                if decl_match:
                    var_name = decl_match.group(2)
                    writes.append(var_name)
                    operation = f"Declaration and assignment of {var_name}"
                    self.add_variable_definition(var_name, i, operation)
                    
                    # Find what it's assigned from
                    assignment_part = line.split('=', 1)[1] if '=' in line else ""
                    reads.extend(self.extract_variables_from_expression(assignment_part))
            
            # Variable declarations without initialization (must come after assignments)
            elif re.search(r'\b(int|char|double|float|long|short|void)\s*\*?\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:,|;)', line):
                # Handle multiple declarations on one line
                type_match = re.search(r'\b(int|char|double|float|long|short|void)\s*(\*?)', line)
                if type_match:
                    var_type = type_match.group(1)
                    is_pointer = type_match.group(2) == '*'
                    
                    # Find all variable names after the type
                    remaining = line[type_match.end():]
                    var_names = re.findall(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:[,;])', remaining)
                    
                    for var_name in var_names:
                        if var_name not in writes:  # Avoid duplicates
                            writes.append(var_name)
                            ptr_str = " pointer" if is_pointer else ""
                            operation = f"Declaration of {var_name}{ptr_str}"
                            self.add_variable_definition(var_name, i, operation)
            
            # Regular assignment operations (var = value)
            elif re.search(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*=', line) and not re.search(r'==', line) and not re.search(r'\*', line):
                assignment_match = re.search(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*=', line)
                if assignment_match:
                    var_name = assignment_match.group(1)
                    writes.append(var_name)
                    operation = f"Assignment to {var_name}"
                    self.add_variable_definition(var_name, i, operation)
                    
                    # Find what it's assigned from
                    assignment_part = line.split('=', 1)[1] if '=' in line else ""
                    reads.extend(self.extract_variables_from_expression(assignment_part))
            
            # Control flow statements (CHECK FIRST before function calls!)
            elif re.search(r'\b(if|while|for)\s*\(', line):
                control_match = re.search(r'\b(if|while|for)\s*\(', line)
                if control_match:
                    control_type = control_match.group(1)
                    operation = f"Control flow: {control_type} statement"
                    
                    # Extract variables from condition
                    paren_start = line.find('(')
                    paren_end = line.find(')')
                    if paren_start != -1 and paren_end != -1:
                        condition = line[paren_start+1:paren_end]
                        reads.extend(self.extract_variables_from_expression(condition))
            
            # Function calls (like printf, scanf, malloc, etc.) - CHECK AFTER control flow
            elif re.search(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*\(', line):
                func_match = re.search(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*\(', line)
                if func_match:
                    func_name = func_match.group(1)
                    operation = f"Function call: {func_name}()"
                    
                    # Extract variables used in function arguments
                    paren_start = line.find('(')
                    paren_end = line.rfind(')')
                    if paren_start != -1 and paren_end != -1:
                        args = line[paren_start+1:paren_end]
                        reads.extend(self.extract_variables_from_expression(args))
                        
                    # Special handling for memory allocation functions
                    if func_name in ['malloc', 'calloc', 'realloc'] and '=' in line:
                        # This is an assignment from malloc
                        assign_match = re.search(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*=', line[:paren_start])
                        if assign_match and assign_match.group(1) not in writes:
                            ptr_var = assign_match.group(1)
                            writes.append(ptr_var)
                            operation = f"Memory allocation: {ptr_var} = {func_name}(...)"
                            self.add_variable_definition(ptr_var, i, operation)
            
            # Return statements
            elif 'return' in line:
                operation = "Return statement"
                return_part = line.split('return', 1)[1] if 'return' in line else ""
                reads.extend(self.extract_variables_from_expression(return_part))
            
            # Add uses for all read variables
            for var in reads:
                self.add_variable_use(var, i, f"Used in: {operation}")
            
            # Store line analysis
            self.line_analysis[i] = {
                'reads': list(set(reads)),
                'writes': list(set(writes)),
                'operation': operation
            }
    
    def extract_variables_from_expression(self, expression):
        """Extract variable names from a C expression"""
        if not expression:
            return []
        
        variables = []
        
        # Remove comments first!
        comment_pos = expression.find('//')
        if comment_pos != -1:
            expression = expression[:comment_pos]
        
        # Handle pointer dereferences (*ptr) as reads
        deref_matches = re.finditer(r'\*\s*([a-zA-Z_][a-zA-Z0-9_]*)', expression)
        for match in deref_matches:
            ptr_name = match.group(1)
            # Add both the pointer (being read) and the dereferenced value
            variables.append(ptr_name)
            variables.append(f"*{ptr_name}")
        
        # Extract variables from function call arguments FIRST
        try:
            func_calls = re.finditer(r'\b[a-zA-Z_][a-zA-Z0-9_]*\s*\(([^)]*)\)', expression)
            for call in func_calls:
                args = call.group(1).strip()
                if args:
                    for arg in args.split(','):
                        arg = arg.strip()
                        if arg and not arg.isdigit():
                            # Check for pointer dereferences in arguments
                            if '*' in arg:
                                deref_match = re.search(r'\*\s*([a-zA-Z_][a-zA-Z0-9_]*)', arg)
                                if deref_match:
                                    ptr_name = deref_match.group(1)
                                    variables.append(ptr_name)
                                    variables.append(f"*{ptr_name}")
                            arg_vars = re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', arg)
                            for var in arg_vars:
                                if var not in ['int', 'char', 'double', 'float', 'NULL', 'sizeof']:
                                    variables.append(var)
        except Exception as e:
            pass
        
        # Filter out C keywords
        c_keywords = {
            'int', 'char', 'double', 'float', 'long', 'short', 'void', 'signed', 'unsigned',
            'if', 'else', 'while', 'for', 'do', 'switch', 'case', 'default', 'break', 'continue',
            'return', 'sizeof', 'typedef', 'struct', 'union', 'enum', 'static', 'extern', 'const',
            'volatile', 'register', 'auto', 'inline', 'restrict', 'NULL'
        }
        
        # Handle array accesses (arr[i])
        array_matches = re.finditer(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*\[([^\]]+)\]', expression)
        for match in array_matches:
            arr_name = match.group(1)
            index_expr = match.group(2)
            # Add the array variable
            variables.append(arr_name)
            # Extract variables from the index expression
            index_vars = re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', index_expr)
            for var in index_vars:
                if var not in c_keywords and len(var) > 0:
                    variables.append(var)
        
        # Remove function calls, string literals, and numbers
        cleaned = re.sub(r'"[^"]*"', '', expression)
        cleaned = re.sub(r"'[^']*'", '', cleaned)
        cleaned = re.sub(r'\b\d+\b', '', cleaned)
        cleaned = re.sub(r'\b[a-zA-Z_][a-zA-Z0-9_]*\s*\([^)]*\)', '', cleaned)
        
        # Remove pointer dereferences we already handled
        cleaned = re.sub(r'\*\s*[a-zA-Z_][a-zA-Z0-9_]*', '', cleaned)
        
        # Remove array accesses from cleaned expression to avoid double-counting
        cleaned = re.sub(r'[a-zA-Z_][a-zA-Z0-9_]*\s*\[[^\]]+\]', '', cleaned)
        
        # Handle struct field access: p.x -> only extract 'p'
        try:
            cleaned = re.sub(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\.[a-zA-Z_][a-zA-Z0-9_]*', r'\1 ', cleaned)
        except Exception as e:
            pass
        
        # Find variable names normally
        var_pattern = r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b'
        matches = re.findall(var_pattern, cleaned)
        
        for match in matches:
            if match not in c_keywords and len(match) > 0:
                variables.append(match)
        
        return list(set(variables))
    
    def add_variable_definition(self, var_name, line_num, details):
        """Add a variable definition"""
        if var_name not in self.variables:
            self.variables[var_name] = {'definitions': [], 'uses': []}
        
        self.variables[var_name]['definitions'].append((line_num, details))
    
    def add_variable_use(self, var_name, line_num, details):
        """Add a variable use"""
        if var_name not in self.variables:
            self.variables[var_name] = {'definitions': [], 'uses': []}
        
        self.variables[var_name]['uses'].append((line_num, details))
    
    def build_dependencies(self):
        """Build variable dependency graph"""
        for line_num, analysis in self.line_analysis.items():
            for written_var in analysis['writes']:
                if written_var not in self.dependencies:
                    self.dependencies[written_var] = []
                
                # Add dependencies on all read variables
                for read_var in analysis['reads']:
                    if read_var != written_var and read_var not in self.dependencies[written_var]:
                        self.dependencies[written_var].append(read_var)
    
    def compute_reaching_definitions(self):
        """Compute which definitions can reach each line"""
        for line_num in self.line_analysis.keys():
            reaching = []
            
            # For each variable used at this line
            analysis = self.line_analysis[line_num]
            for read_var in analysis['reads']:
                if read_var in self.variables:
                    # Find the latest definition before this line
                    latest_def = None
                    for def_line, details in self.variables[read_var]['definitions']:
                        if def_line < line_num:
                            if latest_def is None or def_line > latest_def:
                                latest_def = def_line
                    
                    if latest_def:
                        reaching.append(f"Line {latest_def} (defines {read_var})")
            
            self.reaching_definitions[line_num] = reaching
    
    def build_operation_sequence(self):
        """Build a sequence of operations in C linked list format"""
        operations = []
        operation_id = 0
        
        # Track variable scopes and last definitions for KILL detection
        variable_definitions = {}  # var_name -> line_num of last definition
        
        # Process lines in order to build operation sequence
        for line_num in sorted(self.line_analysis.keys()):
            analysis = self.line_analysis[line_num]
            
            # Process WRITE operations first
            for var in analysis['writes']:
                # Check if this is a redefinition (KILL the previous one)
                if var in variable_definitions:
                    # Add KILL operation for previous definition
                    kill_op = {
                        "operation_id": operation_id,
                        "variable_name": var,
                        "operation": "KILL",
                        "line_number": line_num,
                        "details": f"Variable '{var}' redefined, killing previous definition from line {variable_definitions[var]}",
                        "next": operation_id + 1
                    }
                    operations.append(kill_op)
                    operation_id += 1
                
                # Add WRITE operation
                write_op = {
                    "operation_id": operation_id,
                    "variable_name": var,
                    "operation": "WRITE",
                    "line_number": line_num,
                    "details": analysis['operation'],
                    "next": operation_id + 1
                }
                operations.append(write_op)
                variable_definitions[var] = line_num
                operation_id += 1
            
            # Process READ operations
            for var in analysis['reads']:
                read_op = {
                    "operation_id": operation_id,
                    "variable_name": var,
                    "operation": "READ",
                    "line_number": line_num,
                    "details": analysis['operation'],
                    "next": operation_id + 1
                }
                operations.append(read_op)
                operation_id += 1
            
            # Check for explicit KILL operations (free, end of scope, etc.)
            if line_num <= len(self.lines) and 'free(' in self.lines[line_num - 1]:
                # Extract variable being freed
                free_match = re.search(r'free\s*\(\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*\)', self.lines[line_num - 1])
                if free_match:
                    freed_var = free_match.group(1)
                    kill_op = {
                        "operation_id": operation_id,
                        "variable_name": freed_var,
                        "operation": "KILL",
                        "line_number": line_num,
                        "details": f"Memory freed for variable '{freed_var}'",
                        "next": operation_id + 1
                    }
                    operations.append(kill_op)
                    operation_id += 1
        
        # Update the next pointers - last operation should point to None
        if operations:
            operations[-1]["next"] = None
        
        return operations

    def export_c_linked_list_format(self):
        """Export dataflow analysis in C linked list format"""
        operations = self.build_operation_sequence()
        
        # Build the C-style linked list JSON structure
        c_linked_list = {
            "metadata": {
                "structure_type": "C_LINKED_LIST",
                "node_type": "operation_element",
                "operation_types": ["WRITE", "READ", "KILL"],
                "total_operations": len(operations),
                "list_head": 0 if operations else None,
                "timestamp": datetime.datetime.now().isoformat(),
                "c_dataflow_version": "2.1"
            },
            "type_definitions": {
                "operation_types": {
                    "WRITE": "Variable definition or assignment",
                    "READ": "Variable usage or reference", 
                    "KILL": "Variable goes out of scope, is redefined, or explicitly freed"
                },
                "operation_element": {
                    "operation_id": "int",
                    "variable_name": "string",
                    "operation": "operation_types",
                    "line_number": "int",
                    "details": "string",
                    "next": "int* (pointer to next operation_id, NULL if last)"
                }
            },
            "linked_list_data": operations,
            "c_style_representation": self.generate_c_style_output(operations)
        }
        
        return c_linked_list

    def generate_c_style_output(self, operations):
        """Generate what this would look like in actual C code"""
        c_code_lines = []
        
        # Add type definitions
        c_code_lines.extend([
            "// C Structure Definitions",
            "typedef enum {",
            "    WRITE,",
            "    READ,", 
            "    KILL",
            "} operation_types;",
            "",
            "struct operation_element {",
            "    int operation_id;",
            "    char* variable_name;",
            "    operation_types operation;",
            "    int line_number;",
            "    char* details;",
            "    struct operation_element* next;",
            "};",
            "",
            "// Linked List Nodes (conceptual representation)",
        ])
        
        # Add each operation as a comment showing the linked list structure
        for i, op in enumerate(operations):
            op_type = op['operation']
            var_name = op['variable_name']
            line_num = op['line_number']
            next_id = op['next']
            next_str = f"&node_{next_id}" if next_id is not None else "NULL"
            
            c_code_lines.extend([
                f"// Node {i}:",
                f"// operation_element node_{i} = {{",
                f"//     .operation_id = {op['operation_id']},",
                f"//     .variable_name = \"{var_name}\",",
                f"//     .operation = {op_type},",
                f"//     .line_number = {line_num},",
                f"//     .details = \"{op['details']}\",",
                f"//     .next = {next_str}",
                f"// }};",
                ""
            ])
        
        return "\n".join(c_code_lines)

class TTAGraphAnalyzer:
    """TTA (Timed Task Automaton) Graph analyzer for C code blocks with improved block cutting"""
    
    def __init__(self, code, dataflow_analyzer):
        self.code = code
        self.lines = code.splitlines()
        self.dataflow_analyzer = dataflow_analyzer
        
        # TTA Analysis results
        self.blocks = []  # List of block dictionaries
        self.arcs = []    # List of arc dictionaries
        self.control_flow_stack = []  # Stack to track nested control structures
        
    def analyze(self):
        """Perform comprehensive TTA block analysis"""
        self.create_logical_blocks()
        self.create_control_flow_arcs()
        self.assign_operation_sequences()
    
    def create_logical_blocks(self):
        """Create logical blocks based on control flow structure with improved block cutting"""
        self.blocks = []
        block_id = 0
        
        # Track control flow structures
        control_structures = []  # [(type, start_line, end_line)]
        brace_stack = []  # Track opening braces to find matching closing braces
        
        # First pass: identify control flow structures and their boundaries
        for i, line in enumerate(self.lines):
            line_num = i + 1
            line_stripped = line.strip()
            
            # Skip empty lines and comments
            if not line_stripped or line_stripped.startswith('//') or line_stripped.startswith('#'):
                continue
            
            # Function definition
            if re.search(r'\b(int|char|double|float|long|short|void)\s+main\s*\(', line):
                control_structures.append(('FUNCTION', line_num, None))
                if '{' in line:
                    brace_stack.append(('FUNCTION', line_num))
            
            # Control flow statements
            elif re.search(r'\b(if|for|while)\s*\(', line):
                if 'if' in line:
                    control_structures.append(('IF', line_num, None))
                elif 'for' in line:
                    control_structures.append(('FOR', line_num, None))
                elif 'while' in line:
                    control_structures.append(('WHILE', line_num, None))
                
                if '{' in line:
                    ctrl_type = 'IF' if 'if' in line else ('FOR' if 'for' in line else 'WHILE')
                    brace_stack.append((ctrl_type, line_num))
            
            # else statement
            elif re.search(r'\belse\b', line):
                control_structures.append(('ELSE', line_num, None))
                if '{' in line:
                    brace_stack.append(('ELSE', line_num))
            
            # Track opening braces
            elif '{' in line and not any(keyword in line for keyword in ['if', 'for', 'while', 'else']):
                if brace_stack:
                    brace_stack.append(('BLOCK', line_num))
            
            # Track closing braces
            if '}' in line:
                if brace_stack:
                    ctrl_type, start_line = brace_stack.pop()
                    # Update end lines for control structures
                    for j in range(len(control_structures) - 1, -1, -1):
                        if control_structures[j][1] == start_line and control_structures[j][2] is None:
                            control_structures[j] = (control_structures[j][0], control_structures[j][1], line_num)
                            break
        
        # Second pass: create blocks based on identified structures
        i = 0
        while i < len(self.lines):
            line = self.lines[i]
            line_num = i + 1
            line_stripped = line.strip()
            
            # Skip empty lines and preprocessor directives  
            if not line_stripped or line_stripped.startswith('#'):
                i += 1
                continue
            
            # Function definition - START block
            if re.search(r'\b(int|char|double|float|long|short|void)\s+main\s*\(', line):
                self._create_block(block_id, line_num, line_num, [line], "START")
                block_id += 1
                i += 1
                continue
            
            # Loop statements - LOOP block
            if re.search(r'\b(for|while)\s*\(', line):
                self._create_block(block_id, line_num, line_num, [line], "LOOP")
                block_id += 1
                i += 1
                continue
            
            # If statements - XOR block
            if re.search(r'\bif\s*\(', line):
                self._create_block(block_id, line_num, line_num, [line], "XOR")
                block_id += 1
                i += 1
                continue
            
            # Return statements - include closing brace if it's the function end
            if 'return' in line:
                # Check if next non-empty line is the closing brace of main
                end_line = line_num
                block_lines = [line]
                
                # Look ahead for closing brace
                j = i + 1
                while j < len(self.lines):
                    next_line = self.lines[j]
                    next_line_stripped = next_line.strip()
                    
                    if next_line_stripped == '}':
                        # This is likely the closing brace of main function
                        # Check if this is the last closing brace
                        remaining_braces = sum(1 for k in range(j + 1, len(self.lines)) if '}' in self.lines[k])
                        if remaining_braces == 0:  # This is the last closing brace
                            block_lines.append(next_line)
                            end_line = j + 1
                            i = j  # Skip the closing brace line
                        break
                    elif next_line_stripped and not next_line_stripped.startswith('//'):
                        # Found non-empty, non-comment line that's not a closing brace
                        break
                    j += 1
                
                self._create_block(block_id, line_num, end_line, block_lines, "END")
                block_id += 1
                i += 1
                continue
            
            # else statements - start new block
            if re.search(r'\belse\b', line):
                # else is usually part of the next activity block
                # Find the extent of this else block
                start_line = line_num
                block_lines = []
                
                # If else has opening brace on same line
                if '{' in line:
                    block_lines.append(line)
                    i += 1
                    brace_count = 1
                    
                    # Collect all lines until matching closing brace
                    while i < len(self.lines) and brace_count > 0:
                        current_line = self.lines[i]
                        block_lines.append(current_line)
                        brace_count += current_line.count('{') - current_line.count('}')
                        i += 1
                    
                    # Create activity block for else branch
                    if len(block_lines) > 2:  # More than just else { }
                        self._create_block(block_id, start_line, start_line + len(block_lines) - 1, 
                                         block_lines, "ACTIVITY")
                        block_id += 1
                else:
                    # Single statement else
                    block_lines = [line]
                    if i + 1 < len(self.lines):
                        block_lines.append(self.lines[i + 1])
                        i += 2
                    else:
                        i += 1
                    
                    self._create_block(block_id, start_line, start_line + len(block_lines) - 1, 
                                     block_lines, "ACTIVITY")
                    block_id += 1
                continue
            
            # Opening brace after control structure - start collecting block content
            if '{' in line and i > 0:
                prev_line = self.lines[i - 1].strip()
                if any(keyword in prev_line for keyword in ['if', 'for', 'while', 'else']):
                    # This opening brace belongs to previous control structure
                    # Start collecting sequential statements
                    start_line = line_num
                    block_lines = []
                    i += 1
                    
                    # Collect sequential statements until we hit another control structure or closing brace
                    while i < len(self.lines):
                        current_line = self.lines[i]
                        current_stripped = current_line.strip()
                        
                        # Stop conditions
                        if (re.search(r'\b(if|for|while|else|return)\b', current_stripped) or
                            '}' in current_stripped):
                            break
                        
                        # Add line to current block
                        if current_stripped or current_stripped.startswith('//'):  # Include comments
                            block_lines.append(current_line)
                        
                        i += 1
                    
                    # Create activity block if we collected statements
                    if block_lines:
                        # Filter out empty blocks
                        meaningful_lines = [l for l in block_lines if l.strip() and not l.strip().startswith('//')]
                        if meaningful_lines:
                            self._create_block(block_id, start_line, start_line + len(block_lines) - 1, 
                                             block_lines, "ACTIVITY")
                            block_id += 1
                    continue
            
            # Regular statements - collect sequential statements into activity blocks
            if line_stripped and not line_stripped.startswith('//'):
                start_line = line_num
                block_lines = [line]
                i += 1
                
                # Collect sequential statements
                while i < len(self.lines):
                    current_line = self.lines[i]
                    current_stripped = current_line.strip()
                    
                    # Stop conditions for block boundary
                    if (not current_stripped or  # Empty line
                        current_stripped.startswith('#') or  # Preprocessor
                        re.search(r'\b(if|for|while|else|return)\b', current_stripped) or  # Control flow
                        current_stripped == '}' or  # Closing brace alone
                        ('}' in current_stripped and '{' not in current_stripped)):  # Line with closing brace
                        break
                    
                    # Add line to current block
                    block_lines.append(current_line)
                    i += 1
                
                # Create activity block if meaningful
                meaningful_lines = [l for l in block_lines if l.strip() and not l.strip().startswith('//')]
                if meaningful_lines:
                    self._create_block(block_id, start_line, start_line + len(block_lines) - 1, 
                                     block_lines, "ACTIVITY")
                    block_id += 1
            else:
                i += 1
    
    def _create_block(self, block_id, start_line, end_line, lines, block_type):
        """Create a block with the given parameters"""
        # Filter meaningful lines for preview
        meaningful_lines = [l.strip() for l in lines if l.strip() and not l.strip().startswith('//')]
        
        # Create code preview
        if meaningful_lines:
            preview = meaningful_lines[0]
            if len(preview) > 50:
                preview = preview[:47] + "..."
        else:
            preview = "{ ... }"
        
        block = {
            'block_id': block_id,
            'node_type': block_type,
            'start_line': start_line,
            'end_line': end_line,
            'lines': lines,
            'code_preview': preview,
            'operation_sequence': []
        }
        
        self.blocks.append(block)
    
    def create_control_flow_arcs(self):
        """Create arcs based on logical control flow"""
        self.arcs = []
        
        for i, block in enumerate(self.blocks):
            # START blocks always flow to next block
            if block['node_type'] == 'START':
                if i + 1 < len(self.blocks):
                    self.arcs.append({
                        'from': i,
                        'to': i + 1,
                        'arc_type': 'solid',
                        'description': 'Function entry'
                    })
            
            # ACTIVITY blocks have sequential flow unless they're branches
            elif block['node_type'] == 'ACTIVITY':
                # Check if this is inside a conditional branch
                if self._is_branch_block(i):
                    # Find where branches merge
                    merge_point = self._find_merge_point(i)
                    if merge_point is not None:
                        self.arcs.append({
                            'from': i,
                            'to': merge_point,
                            'arc_type': 'solid',
                            'description': 'Branch to merge'
                        })
                else:
                    # Regular sequential flow
                    if i + 1 < len(self.blocks) and self.blocks[i + 1]['node_type'] != 'END':
                        self.arcs.append({
                            'from': i,
                            'to': i + 1,
                            'arc_type': 'solid',
                            'description': 'Sequential'
                        })
            
            # LOOP blocks
            elif block['node_type'] == 'LOOP':
                # Loop body entry
                if i + 1 < len(self.blocks):
                    self.arcs.append({
                        'from': i,
                        'to': i + 1,
                        'arc_type': 'dashed',
                        'description': 'Loop true'
                    })
                
                # Loop exit
                loop_exit = self._find_loop_exit(i)
                if loop_exit is not None:
                    self.arcs.append({
                        'from': i,
                        'to': loop_exit,
                        'arc_type': 'dashed',
                        'description': 'Loop false'
                    })
                
                # Back edge
                loop_end = self._find_loop_body_end(i)
                if loop_end is not None:
                    self.arcs.append({
                        'from': loop_end,
                        'to': i,
                        'arc_type': 'dotted',
                        'description': 'Loop back'
                    })
            
            # XOR blocks (if statements)
            elif block['node_type'] == 'XOR':
                branches = self._find_xor_branches(i)
                
                if len(branches) >= 1:
                    self.arcs.append({
                        'from': i,
                        'to': branches[0],
                        'arc_type': 'dashed',
                        'description': 'If true'
                    })
                
                if len(branches) >= 2:
                    self.arcs.append({
                        'from': i,
                        'to': branches[1],
                        'arc_type': 'dashed',
                        'description': 'If false'
                    })
    
    def _is_branch_block(self, block_idx):
        """Check if this block is part of a conditional branch"""
        # Look backwards for XOR block
        for i in range(block_idx - 1, max(0, block_idx - 3), -1):
            if self.blocks[i]['node_type'] == 'XOR':
                return True
        return False
    
    def _find_merge_point(self, branch_idx):
        """Find where conditional branches merge"""
        # Simple heuristic: find next non-branch activity or control structure
        current_block = self.blocks[branch_idx]
        
        # Look for the next block that's after the if-else structure
        for i in range(branch_idx + 1, len(self.blocks)):
            block = self.blocks[i]
            # Merge at next control structure or activity that's not a branch
            if block['node_type'] in ['LOOP', 'XOR', 'END']:
                return i
            elif block['node_type'] == 'ACTIVITY' and not self._is_branch_block(i):
                return i
        
        return None
    
    def _find_xor_branches(self, xor_idx):
        """Find the true and false branches of an XOR (if) block"""
        branches = []
        
        # Next block is typically the true branch
        if xor_idx + 1 < len(self.blocks):
            branches.append(xor_idx + 1)
        
        # Look for else branch
        # Search for an activity block that starts with 'else' or comes after the true branch
        true_branch_end = xor_idx + 1
        
        # Find end of true branch
        if true_branch_end < len(self.blocks):
            block = self.blocks[true_branch_end]
            if block['node_type'] == 'ACTIVITY':
                # The false branch should be after this activity
                if true_branch_end + 1 < len(self.blocks):
                    next_block = self.blocks[true_branch_end + 1]
                    # Check if it's an else block
                    if next_block['node_type'] == 'ACTIVITY':
                        # Check if any line contains 'else'
                        has_else = any('else' in line for line in next_block['lines'])
                        if has_else or true_branch_end + 1 == xor_idx + 2:  # Immediate next
                            branches.append(true_branch_end + 1)
        
        return branches
    
    def _find_loop_exit(self, loop_idx):
        """Find where to go when loop condition is false"""
        # Find the block after all loop body blocks
        loop_depth = 0
        
        for i in range(loop_idx + 1, len(self.blocks)):
            block = self.blocks[i]
            
            # Another loop increases depth
            if block['node_type'] == 'LOOP':
                loop_depth += 1
            
            # If we're at depth 0 and find a non-loop-body block
            if loop_depth == 0:
                # Check if this could be outside the loop
                if block['node_type'] in ['XOR', 'LOOP', 'END']:
                    return i
                elif block['node_type'] == 'ACTIVITY':
                    # Check if this activity is after the loop body
                    # Simple heuristic: if it's more than 2 blocks away, it's probably outside
                    if i > loop_idx + 2:
                        return i
            
            # Decrease depth when exiting nested loops
            if loop_depth > 0 and self._is_loop_end(i):
                loop_depth -= 1
        
        # Default to END block
        for i in range(loop_idx + 1, len(self.blocks)):
            if self.blocks[i]['node_type'] == 'END':
                return i
                
        return None
    
    def _find_loop_body_end(self, loop_idx):
        """Find the last block in the loop body"""
        # The last activity block before the loop exit
        last_activity = None
        
        loop_exit = self._find_loop_exit(loop_idx)
        
        for i in range(loop_idx + 1, len(self.blocks)):
            if loop_exit is not None and i >= loop_exit:
                break
                
            block = self.blocks[i]
            if block['node_type'] == 'ACTIVITY':
                last_activity = i
            elif block['node_type'] in ['XOR']:
                # XOR blocks inside loop - the last branch is the end
                branches = self._find_xor_branches(i)
                if branches:
                    last_activity = max(branches)
        
        return last_activity
    
    def _is_loop_end(self, block_idx):
        """Check if this block marks the end of a loop body"""
        if block_idx >= len(self.blocks):
            return False
            
        block = self.blocks[block_idx]
        
        # Check if there's a closing brace that ends a loop
        for line in block['lines']:
            if '}' in line:
                return True
                
        return False
    
    def assign_operation_sequences(self):
        """Assign dataflow operation sequences to each block"""
        if not self.dataflow_analyzer:
            return
        
        operations = self.dataflow_analyzer.build_operation_sequence()
        
        for block in self.blocks:
            block_ops = []
            
            # Find operations within this block's line range
            for op in operations:
                if block['start_line'] <= op['line_number'] <= block['end_line']:
                    block_ops.append(op)
            
            block['operation_sequence'] = block_ops
    
    def export_tta_graph_format(self):
        """Export TTA graph analysis in JSON format"""
        tta_graph = {
            "metadata": {
                "structure_type": "TTA_GRAPH",
                "timestamp": datetime.datetime.now().isoformat(),
                "tta_version": "1.0",
                "total_blocks": len(self.blocks),
                "total_arcs": len(self.arcs)
            },
            "type_definitions": {
                "node_types": ["ACTIVITY", "XOR", "LOOP", "AND", "BLOCK", "START", "END"],
                "operation_types": ["WRITE", "READ", "KILL"],
                "arc_types": ["solid", "dashed", "dotted"],
                "ttagraph_node": {
                    "node_type": "node_types",
                    "operation_sequence": "LinkedList<operation_element>",
                    "solid_arc": "ttagraph_node*",
                    "dashed_arc": "ttagraph_node*",
                    "dotted_arc": "ttagraph_node*"
                }
            },
            "blocks": self.blocks,
            "arcs": self.arcs,
            "c_style_representation": self.generate_tta_c_style_output()
        }
        
        return tta_graph
    
    def generate_tta_c_style_output(self):
        """Generate C-style representation of the TTA graph"""
        c_lines = []
        
        c_lines.extend([
            "// TTA Graph C Structure Definitions",
            "typedef enum {",
            "    ACTIVITY, XOR, LOOP, AND, BLOCK, START, END",
            "} node_types;",
            "",
            "typedef enum {",
            "    WRITE, READ, KILL",
            "} operation_types;",
            "",
            "struct operation_element {",
            "    int operation_id;",
            "    char* variable_name;",
            "    operation_types operation;",
            "    int line_number;",
            "    char* details;",
            "    struct operation_element* next;",
            "};",
            "",
            "struct ttagraph_node {",
            "    node_types node_type;",
            "    struct operation_element* operation_sequence;",
            "    struct ttagraph_node* solid_arc;",
            "    struct ttagraph_node* dashed_arc;",
            "    struct ttagraph_node* dotted_arc;",
            "};",
            "",
            "// TTA Graph Nodes",
        ])
        
        # Add each block as a C node
        for i, block in enumerate(self.blocks):
            c_lines.extend([
                f"// Block {i} - {block['node_type']} (Lines {block['start_line']}-{block['end_line']})",
                f"// Code: {block['code_preview']}",
                f"// ttagraph_node block_{i} = {{",
                f"//     .node_type = {block['node_type']},",
                f"//     .operation_sequence = /* {len(block['operation_sequence'])} operations */,",
                f"//     .solid_arc = /* determined by arcs */,",
                f"//     .dashed_arc = /* determined by arcs */,",
                f"//     .dotted_arc = /* determined by arcs */",
                f"// }};",
                ""
            ])
        
        return "\n".join(c_lines)
    
    def save_graph_image(self, filename):
        """Save TTA graph as image file with improved layout"""
        try:
            # Calculate figure size based on number of blocks
            num_blocks = len(self.blocks)
            fig_height = max(12, num_blocks * 0.8)
            fig_width = max(16, 16 + (num_blocks - 20) * 0.2) if num_blocks > 20 else 16
            
            # Create figure with dynamic size
            fig, ax = plt.subplots(figsize=(fig_width, fig_height))
            fig.patch.set_facecolor('white')
            
            if self.blocks:
                # Create hierarchical layout with better spacing
                pos = self._create_save_layout()
                
                # Draw nodes with better styling
                for i, block in enumerate(self.blocks):
                    x, y = pos[i]
                    
                    # Adaptive node sizing
                    if num_blocks <= 20:
                        box_width, box_height = 2.4, 1.0
                        font_size = 10
                    elif num_blocks <= 40:
                        box_width, box_height = 2.8, 1.2
                        font_size = 9
                    else:
                        box_width, box_height = 3.2, 1.4
                        font_size = 8
                    
                    # Color nodes by type
                    if block['node_type'] == 'START':
                        color = 'lightgreen'
                        edge_color = 'darkgreen'
                    elif block['node_type'] == 'END':
                        color = 'lightcoral'
                        edge_color = 'darkred'
                    elif block['node_type'] == 'XOR':
                        color = 'lightyellow'
                        edge_color = 'orange'
                    elif block['node_type'] == 'LOOP':
                        color = 'lightblue'
                        edge_color = 'darkblue'
                    else:  # ACTIVITY, BLOCK
                        color = 'lightgray'
                        edge_color = 'gray'
                    
                    # Draw node as rectangle
                    box = FancyBboxPatch((x-box_width/2, y-box_height/2), box_width, box_height,
                                        boxstyle="round,pad=0.1",
                                        facecolor=color,
                                        edgecolor=edge_color,
                                        linewidth=2,
                                        alpha=0.9,
                                        zorder=2)
                    ax.add_patch(box)
                    
                    # Add label
                    if num_blocks > 50:
                        label = f"{block['node_type'][0]}{block['node_type'][-1]}\n{block['start_line']}-{block['end_line']}"
                    else:
                        label = f"{block['node_type']}\n(L{block['start_line']}-{block['end_line']})"
                    ax.text(x, y, label, ha='center', va='center', fontsize=font_size, 
                           fontweight='bold', zorder=3)
                
                # Draw edges with curves
                for arc in self.arcs:
                    from_pos = pos[arc['from']]
                    to_pos = pos[arc['to']]
                    
                    dx = to_pos[0] - from_pos[0]
                    dy = to_pos[1] - from_pos[1]
                    
                    # Set edge style - adjust for graph size
                    if arc['arc_type'] == 'solid':
                        color = 'black'
                        linestyle = '-'
                        linewidth = 2 if num_blocks <= 30 else 1.5
                        connectionstyle = "arc3,rad=0.1"
                    elif arc['arc_type'] == 'dashed':
                        color = 'blue'
                        linestyle = '--'
                        linewidth = 2.5 if num_blocks <= 30 else 2
                        connectionstyle = "arc3,rad=0.3" if dx != 0 else "arc3,rad=0.2"
                    else:  # dotted
                        color = 'red'
                        linestyle = ':'
                        linewidth = 3 if num_blocks <= 30 else 2.5
                        connectionstyle = "arc3,rad=-0.5"
                    
                    # Calculate connection points
                    if num_blocks <= 20:
                        y_offset = box_height/2
                        x_offset = box_width/2
                    elif num_blocks <= 40:
                        y_offset = box_height/2
                        x_offset = box_width/2
                    else:
                        y_offset = box_height/2
                        x_offset = box_width/2
                    
                    if dy < 0:
                        from_y = from_pos[1] - y_offset
                        to_y = to_pos[1] + y_offset
                    else:
                        from_y = from_pos[1] + y_offset
                        to_y = to_pos[1] - y_offset
                    
                    if dx > 0:
                        from_x = from_pos[0] + x_offset * 0.8
                        to_x = to_pos[0] - x_offset * 0.8
                    elif dx < 0:
                        from_x = from_pos[0] - x_offset * 0.8
                        to_x = to_pos[0] + x_offset * 0.8
                    else:
                        from_x = from_pos[0]
                        to_x = to_pos[0]
                    
                    ax.annotate('', xy=(to_x, to_y), xytext=(from_x, from_y),
                               arrowprops=dict(arrowstyle='->', 
                                             color=color, 
                                             linestyle=linestyle, 
                                             linewidth=linewidth,
                                             connectionstyle=connectionstyle,
                                             shrinkA=5, shrinkB=5),
                               zorder=1)
                
                # Title removed to prevent cutoff
                # plt.title("TTA Control Flow Graph", fontsize=18, fontweight='bold', pad=20)
                
                # Add legend - positioned at bottom
                legend_elements = [
                    Line2D([0], [0], color='black', lw=2, label='Sequential'),
                    Line2D([0], [0], color='blue', lw=2.5, linestyle='--', label='Conditional'),
                    Line2D([0], [0], color='red', lw=3, linestyle=':', label='Loop Back')
                ]
                ax.legend(handles=legend_elements, 
                         loc='lower center', 
                         bbox_to_anchor=(0.5, -0.1),
                         ncol=3,
                         fontsize=11, 
                         framealpha=0.9,
                         borderaxespad=0)
                
                # Set axis limits
                all_x = [p[0] for p in pos.values()]
                all_y = [p[1] for p in pos.values()]
                
                x_padding = 3 if num_blocks > 30 else 2
                y_padding = 2 if num_blocks > 30 else 1.5
                
                ax.set_xlim(min(all_x) - x_padding, max(all_x) + x_padding)
                ax.set_ylim(min(all_y) - y_padding, max(all_y) + y_padding)
                
                grid_alpha = 0.1 if num_blocks > 30 else 0.2
                ax.grid(True, alpha=grid_alpha, linestyle='--')
            
            # Adjust aspect ratio for very tall graphs
            if num_blocks > 40:
                ax.set_aspect('auto')
            else:
                ax.set_aspect('equal')
            ax.axis('off')
            plt.tight_layout(rect=[0, 0.05, 1, 0.98])  # Adjusted spacing without title
            plt.savefig(filename, dpi=300, bbox_inches='tight', facecolor='white')
            plt.close(fig)
            
        except Exception as e:
            raise Exception(f"Could not save TTA graph: {str(e)}")
    
    def _create_save_layout(self):
        """Create layout for saving - similar to display layout"""
        pos = {}
        
        # Calculate dynamic spacing based on number of blocks
        num_blocks = len(self.blocks)
        
        # Adaptive spacing parameters
        if num_blocks <= 15:
            x_center = 6
            x_branch_offset = 4
            y_spacing = 2.5
        elif num_blocks <= 30:
            x_center = 8
            x_branch_offset = 5
            y_spacing = 3.5
        else:
            x_center = 10
            x_branch_offset = 6
            y_spacing = 4.5
            
        y_level = num_blocks * y_spacing * 1.2
        
        positioned = set()
        
        for i, block in enumerate(self.blocks):
            if i in positioned:
                continue
                
            block_type = block['node_type']
            
            if block_type == 'START':
                pos[i] = (x_center, y_level)
                y_level -= y_spacing
                positioned.add(i)
                
            elif block_type == 'LOOP':
                pos[i] = (x_center, y_level)
                y_level -= y_spacing
                positioned.add(i)
                
            elif block_type == 'XOR':
                pos[i] = (x_center, y_level)
                branches = self._find_xor_branches(i)
                branch_y = y_level - y_spacing
                
                if len(branches) >= 1 and branches[0] not in positioned:
                    pos[branches[0]] = (x_center - x_branch_offset, branch_y)
                    positioned.add(branches[0])
                
                if len(branches) >= 2 and branches[1] not in positioned:
                    pos[branches[1]] = (x_center + x_branch_offset, branch_y)
                    positioned.add(branches[1])
                
                y_level -= (y_spacing * 2.5 + y_spacing * 0.6)
                positioned.add(i)
                
            elif block_type == 'END':
                pos[i] = (x_center, y_spacing * 2)
                positioned.add(i)
                
            else:  # ACTIVITY
                if i not in positioned:
                    pos[i] = (x_center, y_level)
                    y_level -= y_spacing
                    positioned.add(i)
        
        return pos

if __name__ == "__main__":
    try:
        # Set matplotlib to non-interactive mode to prevent thread issues
        plt.ioff()
        
        c_sde = CSyntaxDirectedEnvironment()
        c_sde.run()
    except ImportError as e:
        if "networkx" in str(e) or "matplotlib" in str(e):
            print("Missing required libraries. Please install:")
            print("pip install networkx matplotlib")
        else:
            print(f"Import error: {e}")
    except KeyboardInterrupt:
        print("\nApplication interrupted by user")
        sys.exit(0)
    except Exception as e:
        print(f"Error starting application: {e}")
        sys.exit(1)