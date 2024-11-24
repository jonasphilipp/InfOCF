Signatur
 	c,			% 1.Chronische Myeloische Leukämie (CML)
	a,			% 2.Atypische Chronische Myeloische Leukämie (aCML)
	b,			% 3.Die BCR-ABL Translokation haben
	g,			% 4.Eine günstige Prognose haben
	m,			% 5.Eine allogene hämatopoetische Stammzelltransplanta-tion (HSCT) bekommen
	r			% 6.Eine schwere Transplant-gegen-Wirt-Reaktion haben (Graft-versus-Host-Disease: GvHD)

Konditionale
CML6 {
	(b|c),		% 1.CML zeichnet sich typischerweise durch eine Fusion der beiden Gene ABL und BCR aus.
	(g|b),		% 2.Wenn man ein BCR-ABL-Fusionsgen hat, so deutet dies normalerweise auf eine günstige Prognose hin.
	(c|a),		% 3.Atypische Chronische Myeloische Leukämie ist eine Form von CML.
	(!b|a),		% 4.Bei der aCML lässt sich die Fusion der beiden Gene ABL und BCR nicht nachweisen.
	(g|m),		% 5.Bei einer allogenen HSCT ist die Prognose meistens günstig. 
	(!g|m,r)	% 6.Bei einer allogenen HSCT mit einer schweren GvHD ist die Prognose meistens ungünstig. 
}
