Signatur
	m,		% 1.Säugetiere (mammals)
	u,		% 2.Ein Fell aus Haaren haben (to have a fur)
	v,		% 3.Lebendgebärend sein (to be viviparous)
	s		% 4.Schnabeltiere (platypuses)

Konditionale
SAEUGETIERE4 {
	(u|m),		% 1.Säugetiere haben meistens ein Fell aus Haaren.
	(v|m),		% 2.Säugetiere sind meistens lebendgebärend.
	(m|s),		% 3.Schnabeltiere sind Säugetiere.
	(!v|s)		% 4.Schnabeltiere sind nicht lebendgebärend.
}
