Signatur
	m,			% 1.Säugetiere (mammals)
	v,			% 2.Lebendgebärend sein (to be viviparous)
	u,			% 3.Ein Fell aus Haaren haben (to have a fur)
	c,			% 4.Eine Plazenta haben (to have placenta)
	e,			% 5.Beuteltiere (marsupials)
	k			% 6.Kloakentiere (monotremata)

Konditionale
SAEUGETIERE7 {
	(v|m),		% 1.Säugetiere sind meistens lebendgebärend.
	(c|m),		% 2.Säugetiere haben meistens eine Plazenta.
	(u|m),		% 3.Säugetiere haben meistens ein Fell aus Haaren.
	(m|e),		% 4.Beuteltiere sind Säugetiere.
	(!c|e),		% 5.Beuteltiere haben keine Plazenta.
	(m|k),		% 6.Kloakentiere sind Säugetiere.
	(!v,!c|k)	% 7.Kloakentiere sind nicht lebendgebärend und haben keine Plazenta.
}


