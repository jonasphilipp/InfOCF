Signatur
	w,			% 1.Wirbeltiere (vertebrates)
	i,			% 2.Eine Wirbelsäule haben (to have a spinal column)
	m,			% 3.Säugetiere (mammals)
	v,			% 4.Lebendgebärend sein (to be viviparous)
	c,			% 5.Eine Plazenta haben (to have placenta)
	e,			% 6.Beuteltiere (marsupials)
	k,			% 7.Kloakentiere (monotremata)
	s,			% 8.Sauropsiden (sauropsida)
	g,			% 9.Eier legen an Land (to lay eggs on land)
	b,			% 10.Vögel (birds)
	f,			% 11.Fliegen können (to fly)
	u			% 12.Ein Fell aus Haaren haben (to have a fur)

Konditionale
WIRBELTIERE13 {
	(i|w),		% 1.Wirbeltiere haben meistens eine Wirbelsäule.
	(w|m),		% 2.Säugetiere sind Wirbeltiere.
	(v|m),		% 3.Säugetiere sind meistens lebendgebärend.
	(c|m),		% 4.Säugetiere haben meistens eine Plazenta.
	(m|e),		% 5.Beuteltiere sind Säugetiere.
	(!c|e),		% 6.Beuteltiere haben meistens keine Plazenta.
	(m|k),		% 7.Kloakentiere sind Säugetiere.
	(!v,!c|k),	% 8.Kloakentiere sind nicht lebendgebärend und haben keine Plazenta.
	(w|s),		% 9.Sauropsiden sind Wirbeltiere.
	(g|s),		% 10.Sauropsiden legen meistens Eier an Land.
	(s|b),		% 11.Vögel sind Sauropsiden.
	(f|b)		% 12.Vögel können typischerweise fliegen.
	(u|m),		% 13.Säugetiere haben meistens ein Fell aus Haaren.
}
