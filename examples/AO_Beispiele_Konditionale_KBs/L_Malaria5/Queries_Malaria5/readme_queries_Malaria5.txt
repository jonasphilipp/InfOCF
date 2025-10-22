MALARIA5: Queries

	(m|h),			% Erkranken Menschen, die sich mit dem Malariaerreger infiziert haben, normalerweise schwer an Malaria?
					% Plausible Antwort: Ja.

	(m|s),			% Erlaubt ein Sichelzellengen  normalerweise schwer an Malaria zu erkranken?
					% Plausible Antwort: Nein.

	(m|h,!s),		% Erkranken Menschen, die sich mit dem Malariaerreger infiziert haben und kein Sichelzellengen aufweisen, normalerweise schwer an Malaria?
					% Plausible Antwort: Ja.

	(m|h,s),		% Erkranken Menschen, die sich mit dem Malariaerreger infiziert haben und ein Sichelzellengen aufweisen, normalerweise schwer an Malaria?
					% Plausible Antwort: Nein.

	(m|h,p),		% Erkranken Menschen, die sich mit dem Malariaerreger infiziert haben und eine Chemoprophylaxe anwenden, normalerweise schwer an Malaria?
					% Plausible Antwort: Nein.

	(m|h,p,r),		% Erkranken Menschen, die sich mit dem Malariaerreger infiziert haben, eine Malariaprophylaxe anwenden und beim Malariaerreger eine Resistenz gegen diese Prophylaxe vorliegt, normalerweise schwer an Malaria?
					% Plausible Antwort: Ja.

	(m|h,p,r,s)		% Erkranken Menschen, die sich mit dem Malariaerreger infiziert haben, ein Sichelzellengen aufweisen, bei der Anwendung einer Malariaprophylaxe und dem Vorliegen einer Resistenz dagegen, normalerweise schwer an Malaria: (m|hprs)?
					% Plausible Antwort: Nein.
