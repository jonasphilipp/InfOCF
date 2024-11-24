ALL3: Queries

	(g|a,!o),		% Hat die ALL, wenn man ein bestimmtes Patientenalter (jünger als 1 Jahr oder älter als 13 Jahre) nicht hat, eine günstige Prognose?
					% Plausible Antwort: Ja.

	(g|a,!o,p),		% Hat die ALL, wenn man ein bestimmtes Patientenalter (jünger als 1 Jahr oder älter als 13 Jahre) nicht hat und eine hohe Zahl an weißen Blutzellen im Blut vorkommt, eine günstige Prognose?
					% Plausible Antwort: Nein.
	
	(g|a,!o,p,t)	% Hat die ALL, wenn man ein bestimmtes Patientenalter (jünger als 1 Jahr oder älter als 13 Jahre) nicht hat, eine hohe Zahl an weißen Blutzellen im Blut hat (p) und eine ziel-gerichtete Therapie (t) vorhanden ist, eine günstige Prognose?
					% Plausible Antwort: Ja.







