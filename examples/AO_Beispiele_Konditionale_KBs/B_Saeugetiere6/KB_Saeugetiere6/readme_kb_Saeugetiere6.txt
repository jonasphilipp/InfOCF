Signatur
	m,			% 1.Säugetiere (mammals)
	v,			% 2.Lebendgebärend sein (to be viviparous)
	c,			% 3.Eine Plazenta haben (to have placenta)
	e,			% 4.Beuteltiere (marsupials)
	k			% 5.Kloakentiere (monotremata)

Konditionale
SAEUGETIERE6 {
	(v|m),		% 1.Säugetiere sind meistens lebendgebärend.
	(c|m),		% 2.Säugetiere haben meistens eine Plazenta.
	(m|e),		% 3.Beuteltiere sind Säugetiere.
	(!c|e),		% 4.Beuteltiere haben keine Plazenta.
	(m|k),		% 5.Kloakentiere sind Säugetiere.
	(!v,!c|k)	% 6.Kloakentiere sind nicht lebendgebärend und haben keine Plazenta.
}
