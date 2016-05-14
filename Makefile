TOP ="frontend.py"
OUTPUT = "analysis.txt"
PYTHON_VER = "python2"

compileAndRedirect:
	$(PYTHON_VER) $(TOP) > $(OUTPUT)

compile: 
	$(PYTHON_VER) $(TOP)


clean: 
	rm $(OUTPUT)
