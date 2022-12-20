all:
	happy -gca ParLI.y
	alex -g LexLI.x
	ghc --make TestLI.hs -o TestLI

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocLI.* LexLI.* ParLI.* LayoutLI.* SkelLI.* PrintLI.* TestLI.* AbsLI.* TestLI ErrM.* SharedString.* ComposOp.* LI9.dtd XMLLI.* Makefile*
	

