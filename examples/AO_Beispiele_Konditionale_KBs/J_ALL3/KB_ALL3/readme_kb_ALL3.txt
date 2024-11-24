Signatur
 	a,			% 1.Akute Lymphatische Leukämie
	g,			% 2.Eine günstige Prognose haben
	o,			% 3.Ein bestimmtes Patientenalter: Jünger als 1 Jahr oder älter als 13 Jahre
	p,			% 4.Hohe Zahl der weißen Blutzellen im Blut
	s,			% 5.Befall des Zentralennervensystems
	u,			% 6.T-Linien ALL
	v,			% 7.Verminderung der Chromosomenzahl
	w,			% 8.Trisomie von Chromosom 21
	x,			% 9.KMT2A-Aberrationen
	y,			% 10.Steroidannahme vor der Diagnose
	z,			% 11.Verzögertes Ansprechen auf die Therapie
	t			% 12.Gezielte Therapie vorhanden

Konditionale
ALL3 {
	(g|a),		% 1.Akute Lymphatische Leukämie hat normalerweise eine günstige Prognose.
	(!g|a,(o;p;s;u;v;w;x;y;z)),		
				% 2.Wenn man ALL und eines der unter „o“ bis „z“ ausgewiesenen Merkmale hat, 
				% so deutet dies normalerweise auf eine ungünstige Prognose hin.
	(g|a,(o;p;s;u;v;w;x;y;z),t)		
				% 3.Wenn man ALL, eines der unter „o“ bis „z“ ausgewiesenen Merkmale hat 
				% und eine gezielte Therapie vorhanden ist, so deutet dies normalerweise auf eine günstige Prognose hin.
}
