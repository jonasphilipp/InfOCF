Signatur
 	b,			% 1.B-Zellen
	l,			% 2.Gedächtnis-B-Zellen (long term memory B-cells)
	n,			% 3.CD19-Rezeptor haben
	m,			% 4.IgM-Rezeptor haben
	g			% 5.IgG-Rezeptor haben

Konditionale
BZELLEN5 {
	(n|b),		% 1.B-Zellen haben meistens einen CD19-Rezeptor.
	(m|b),		% 2.B-Zellen haben meistens einen IgM-Rezeptor.
	(b|l),		% 3.Gedächtnis-B-Zellen sind B-Zellen.
	(!m|l),		% 4.Gedächtnis-B-Zellen haben meistens keinen IgM-Rezeptor.
	(g|l)		% 5.Gedächtnis-B-Zellen haben vorwiegend einen IgG-Rezeptor.
}
