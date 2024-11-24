Signatur
 	t,			% 1.T-Zellen
 	h,			% 2.T-Helferzellen
	z,			% 3.Zytotoxische T-Zellen
	d,			% 4.CD3-Rezeptor haben
	v,			% 5.CD4-Rezeptor haben
	a			% 6.CD8-Rezeptor haben

Konditionale
TZELLEN6 {
	(d|t),		% 1.T-Zellen haben meistens einen CD3-Rezeptor.
	(t|h),		% 2.T-Helferzellen sind T-Zellen.
	(v|h),		% 3.T-Helferzellen haben meistens einen CD4-Rezeptor.
	(h|d,v),	% 4.Die Zellen, die einen CD3-Rezeptor und einen CD4-Rezeptor haben, sind meistens T-Helferzellen.
	(t|z),		% 5.Zytotoxische T-Zellen sind T-Zellen.
	(a|z)		% 6.Zytotoxische T-Zellen haben meistens einen CD8-Rezeptor.
}
