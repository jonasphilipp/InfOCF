Signatur
 	w,			% 1.Wirbeltiere (vertebrates)
	i,			% 2.Eine Wirbelsäule haben (to have a spinal column)
	m,			% 3.Säugetiere (mammals)
	u,			% 4.Ein Fell aus Haaren haben (to have a fur)
	v,			% 5.Lebendgebärend sein (to be viviparous)
	c,			% 6.Eine Plazenta haben (to have placenta)
	e,			% 7.Beuteltiere (marsupials)
	k,			% 8.Kloakentiere (monotremata)
	s,			% 9.Sauropsiden (sauropsida)
	o,			% 10.Farben sehen (to see colours)
	g,			% 11.Eier legen an Land (to lay eggs on land)
	b,			% 12.Vögel (birds)
	f,			% 13.Fliegen können (to fly)
	p,			% 14.Pinguine (penguins)
	r,			% 15.Reptilien (reptiles)
	d,			% 16.Eine trockene Haut mit Hornschuppen haben (to have a dry, horny skin)
	a,			% 17.Amphibien (amphibia)
	j,			% 18.Eier im Wasser legen (to lay eggs in water)
	h,			% 19.Fische (fish)
	l,			% 20.Mit Kiemen atmen (to breathe with gills)
	n			% 21.Rundmäuler (cyclostomata)

Konditionale
WIRBELTIERE24 {
	(i|w),		% 1.Wirbeltiere haben meistens eine Wirbelsäule.
	(w|m),		% 2.Säugetiere sind Wirbeltiere.
	(u|m),		% 3.Säugetiere haben meistens ein Fell aus Haaren.
	(v|m),		% 4.Säugetiere sind meistens lebendgebärend.
	(c|m),		% 5.Säugetiere haben meistens eine Plazenta.
	(m|e),		% 6.Beuteltiere sind Säugetiere.
	(!c|e),		% 7.Beuteltiere haben meistens keine Plazenta.
	(m|k),		% 8.Kloakentiere sind Säugetiere.
	(!v,!c|k),	% 9.Kloakentiere sind nicht lebendgebärend und haben keine Plazenta.
	(w|s),		% 10.Sauropsiden sind Wirbeltiere.
	(o|s),		% 11.Sauropsiden können meistens Farben sehen.
	(g|s),		% 12.Sauropsiden legen meistens Eier an Land.
	(s|b),		% 13.Vögel sind Sauropsiden.
	(f|b),		% 14.Vögel können typischerweise fliegen.
	(b|p),		% 15.Pinguine sind Vögel.
	(!f|p),		% 16.Pinguine können nicht fliegen.
	(s|r),		% 17.Reptilien sind Sauropsiden.
	(d|r),		% 18.Reptilien haben normalerweise eine trockene Haut mit Hornschuppen.
	(w|a),		% 19.Amphibien sind Wirbeltiere.
	(j|a),		% 20.Amphibien legen typischerweise Eier im Wasser.
	(w|h),		% 21.Fische sind Wirbeltiere.
	(l|h),		% 22.Fische atmen typischerweise mit Kiemen.
	(w|n),		% 23.Rundmäuler sind Wirbeltiere.
	(!i|n)		% 24.Rundmäuler haben typischerweise keine Wirbelsäule. 
}
