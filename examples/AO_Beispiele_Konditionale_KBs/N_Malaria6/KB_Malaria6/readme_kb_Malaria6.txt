Signatur
	h,			% 1.Menschen, die sich mit dem Malariaerreger infiziert haben (humans infected with malaria pathogen)
	m,			% 2.Schwer an Malaria erkranken (to get seriously sick with malaria)
	s,			% 3.Eine Sichelzellanämie-Variante des Hämoglobins haben (to have have sickle cell anemia version of hemoglobin gene) 
	p,			% 4.Eine Chemoprophylaxe anwenden
	r			% 5.Das Vorliegen einer Resistenz gegen die Chemoprophy-laxe beim Malariaerreger

Konditionale
MALARIA6 {
	(!s|h),		% 1.Menschen, die sich mit dem Malariaerreger infiziert haben, haben normalerweise kein Sichelzellengen.
	(m|!s),		% 2.Ein fehlendes Sichelzellengen erlaubt es normaler-weise, schwer an Malaria zu erkranken.
	(m|h), 		% 3.Menschen, die sich mit dem Malariaerreger infiziert haben, erkranken normalerweise schwer an Malaria.
	(!m|s),		% 4.Ein Sichelzellengen erlaubt es normalerweise nicht, schwer an Malaria zu erkranken.
	(!m|p),		% 5.Die Anwendung einer Chemoprophylaxe erlaubt es nor-malerweise nicht, schwer an Malaria zu erkranken.
	(m|p,r)		% 6.Die Anwendung einer Chemoprophylaxe und das Vorlie-gen einer Resistenz dagegen beim Malariaerreger erlauben es normalerweise, schwer an Malaria zu erkranken.
}


