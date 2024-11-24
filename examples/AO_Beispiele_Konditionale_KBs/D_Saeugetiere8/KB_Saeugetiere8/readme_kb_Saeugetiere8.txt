Signatur
	m,			% 1.Säugetiere (mammals)
	v,			% 2.Lebendgebärend sein (to be viviparous)
	u,			% 3.Ein Fell aus Haaren haben (to have a fur)
	o,			% 4.Farben gut sehen (to see colours)
	c,			% 5.Eine Plazenta haben (to have placenta)
	e,			% 6.Beuteltiere (marsupials)
	k			% 7.Kloakentiere (monotremata)

Konditionale
SAEUGETIERE8 {
	(v|m),		% 1.Säugetiere sind meistens lebendgebärend.
	(c|m),		% 2.Säugetiere haben meistens eine Plazenta.
	(u|m),		% 3.Säugetiere haben meistens ein Fell aus Haaren.
	(!o|m),		% 4.Säugetiere sehen Farben meistens nicht gut.
	(m|e),		% 5.Beuteltiere sind Säugetiere.
	(!c|e),		% 6.Beuteltiere haben keine Plazenta.
	(m|k),		% 7.Kloakentiere sind Säugetiere.
	(!v,!c|k)	% 8.Kloakentiere sind nicht lebendgebärend und haben keine Plazenta.
}
