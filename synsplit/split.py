"""
split.py: Erweiterung synsplit für InfOCF

Dieses Modul implementiert ein Verfahren zur Berechnung konditionaler Syntax-Splittings für konditionale Wissensbasen.
Details zu den Algorithmen und der verwendeten Literatur sind in der Masterarbeit „Entwicklung und Implementierung eines
Verfahrens zur Bestimmung konditionaler Syntax Splittings“ dokumentiert.

Autor: Franziska Herkner
Datum: 30.09.2025
"""

import os
import time
from itertools import product

from more_itertools import powerset_of_sets
from pysmt.shortcuts import Bool, Symbol, get_atoms

from inference.conditional import Conditional
from parser.Wrappers import parse_belief_base


def main():
    # cl_file_path = os.path.join('examples', '484_inference_relations_representatives', 'kb4.cl')
    # cl_file_path = os.path.join('examples', 'master', 'delta_large.cl')
    # cl_file_path = os.path.join('examples', 'master', 'delta_sun.cl')
    cl_file_path = os.path.join(
        "examples",
        "AO_Beispiele_Konditionale_KBs",
        "B_Saeugetiere6",
        "KB_Saeugetiere6",
        "kb_Saeugetiere6.cl",
    )

    start_time = time.time()
    calc_all_conditional_syntax_splittings(cl_file_path)
    end_time = time.time()
    elapsed = end_time - start_time
    print(f"Laufzeit: {elapsed:.4f} Sekunden")


def calc_all_conditional_syntax_splittings(cl_file_path):
    """
    Berechnung aller Varianten konditionaler Syntax-Splittings zu gegebener .cl-Datei
    """
    print(f"file name: {cl_file_path}\n")

    # Signatur und Wissensbasis einlesen aus .cl-Datei
    belief_base = parse_belief_base(cl_file_path)
    sigma = set(belief_base.signature)
    delta = set(belief_base.conditionals.values())

    print(f"Sigma: {sigma}\nDelta: {delta}\n")

    # Berechnung aller Varianten konditionaler Syntax-Splittings inkl. Ausgabe der Anzahl im Terminal
    cond_splittings = calculate_conditional_syntax_splittings(sigma, delta)
    print(f"Anzahl konditionaler Syntax-Splittings: {len(cond_splittings)}\n")

    genuine_splittings = filter_genuine_splittings(cond_splittings)
    print(
        f"Anzahl genuiner konditionaler Syntax-Splittings: {len(genuine_splittings)}\n"
    )

    safe_splittings = filter_safe_conditional_syntax_splittings(cond_splittings)
    print(f"Anzahl sicherer konditionaler Syntax-Splittings: {len(safe_splittings)}\n")

    genuine_safe_splittings = filter_genuine_splittings(safe_splittings)
    print(
        f"Anzahl genuiner sicherer konditionaler Syntax-Splittings: {len(genuine_safe_splittings)}\n"
    )

    generalized_safe_splittings = filter_safe_conditional_syntax_splittings(
        cond_splittings, generalized=True
    )
    print(
        f"Anzahl generalisierter sicherer konditionaler Syntax-Splittings: {len(generalized_safe_splittings)}\n"
    )

    genuine_generalized_safe_splittings = filter_genuine_splittings(
        generalized_safe_splittings
    )
    print(
        f"Anzahl genuiner generalisierter sicherer konditionaler Syntax-Splittings: {len(genuine_generalized_safe_splittings)}\n"
    )

    # Ausgabe ermittelter Varianten konditionaler Syntax-Splittings in eine Datei (zu viele Daten für Terminal)
    write_output_to_file(
        sigma,
        delta,
        cond_splittings,
        genuine_splittings,
        safe_splittings,
        genuine_safe_splittings,
        generalized_safe_splittings,
        genuine_generalized_safe_splittings,
    )


def write_output_to_file(
    sigma,
    delta,
    cond_splittings,
    genuine_splittings,
    safe_splittings,
    genuine_safe_splittings,
    generalized_safe_splittings,
    genuine_generalized_safe_splittings,
):
    """
    Schreibt alle ermittelten Variante konditionaler Syntax-Splittings in eine Datei
    """

    output_dir = os.path.join("synsplit", "output")
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, "splittings_output.txt")

    with open(output_file, "w", encoding="utf-8") as f:
        f.write(f"Sigma: {sigma}\nDelta: {delta}\n\n")

        f.write("Konditionale Syntax-Splittings:\n\n")
        for sigma3, sigma1, sigma2, delta1, delta2 in cond_splittings:
            f.write(f"Sigma3: {sigma3}\nSigma1: {sigma1}, Sigma2: {sigma2}\n")
            f.write(f"Delta1: {delta1}, Delta2: {delta2}\n\n")

        f.write("Genuine konditionale Syntax-Splittings:\n\n")
        for sigma3, sigma1, sigma2, delta1, delta2 in genuine_splittings:
            f.write(f"Sigma3: {sigma3}\nSigma1: {sigma1}, Sigma2: {sigma2}\n")
            f.write(f"Delta1: {delta1}, Delta2: {delta2}\n\n")

        f.write("Sichere konditionale Syntax-Splittings:\n\n")
        for sigma3, sigma1, sigma2, delta1, delta2 in safe_splittings:
            f.write(f"Sigma3: {sigma3}\nSigma1: {sigma1}, Sigma2: {sigma2}\n")
            f.write(f"Delta1: {delta1}, Delta2: {delta2}\n\n")

        f.write("Genuine sichere konditionale Syntax-Splittings:\n\n")
        for sigma3, sigma1, sigma2, delta1, delta2 in genuine_safe_splittings:
            f.write(f"Sigma3: {sigma3}\nSigma1: {sigma1}, Sigma2: {sigma2}\n")
            f.write(f"Delta1: {delta1}, Delta2: {delta2}\n\n")

        f.write("Generalisierte sichere konditionale Syntax-Splittings:\n\n")
        for sigma3, sigma1, sigma2, delta1, delta2 in generalized_safe_splittings:
            f.write(f"Sigma3: {sigma3}\nSigma1: {sigma1}, Sigma2: {sigma2}\n")
            f.write(f"Delta1: {delta1}, Delta2: {delta2}\n\n")

        f.write("Genuine generalisierte sichere konditionale Syntax-Splittings:\n\n")
        for (
            sigma3,
            sigma1,
            sigma2,
            delta1,
            delta2,
        ) in genuine_generalized_safe_splittings:
            f.write(f"Sigma3: {sigma3}\nSigma1: {sigma1}, Sigma2: {sigma2}\n")
            f.write(f"Delta1: {delta1}, Delta2: {delta2}\n\n")

    print(f"Ausgabe gespeichert in: {output_file}\n")


def in_sigma3_only(conditional, sigma3):
    """
    Überprüfung, ob Konditional-Atome nur in Sigma3 vorkommen
    """
    return atoms(conditional.consequence).issubset(sigma3) and atoms(
        conditional.antecedence
    ).issubset(sigma3)


def filter_safe_conditional_syntax_splittings(splittings, generalized=False):
    """
    Filtern sicherer konditionaler Syntax-Splittings aus konditionalen Syntax-Splittings.

    Wenn generalized=False:
        alle Konditionale aus Delta komplett prüfen
    Wenn generalized=True:
        Konditionale, die nur in sigma3 vorkommen, ignorieren
    """
    safe_splittings = []

    for sigma3, sigma1, sigma2, delta1, delta2 in splittings:
        # Relevante Konditionale auswählen
        if generalized:
            delta1_relevant = {
                conditional
                for conditional in delta1
                if not in_sigma3_only(conditional, sigma3)
            }
            delta2_relevant = {
                conditional
                for conditional in delta2
                if not in_sigma3_only(conditional, sigma3)
            }
        else:
            delta1_relevant = delta1
            delta2_relevant = delta2

        # i = 1, j = 2
        safe_delta2 = all(
            any(
                all(
                    not (
                        interpretation_is_true(
                            conditional.antecedence, {**omega13, **omega2}
                        )
                        and not interpretation_is_true(
                            conditional.consequence, {**omega13, **omega2}
                        )
                    )
                    for conditional in delta2_relevant
                )
                for omega2 in interpretations(sigma2)
            )
            for omega13 in interpretations(sigma1.union(sigma3))
        )

        # i = 2, j = 1

        # Delta1 nur prüfen, wenn Delta2 safe ist
        safe_delta1 = False
        if safe_delta2:
            safe_delta1 = all(
                any(
                    all(
                        not (
                            interpretation_is_true(
                                conditional.antecedence, {**omega23, **omega1}
                            )
                            and not interpretation_is_true(
                                conditional.consequence, {**omega23, **omega1}
                            )
                        )
                        for conditional in delta1_relevant
                    )
                    for omega1 in interpretations(sigma1)
                )
                for omega23 in interpretations(sigma2.union(sigma3))
            )

        if safe_delta1 and safe_delta2:
            safe_splittings.append((sigma3, sigma1, sigma2, delta1, delta2))

    return safe_splittings


def interpretations(atoms):
    """
    Generieren aller möglichen Interpretationen atomarer Formeln
    """
    atoms = sorted(atoms)  # Sortieren für Konsistenz
    truth_values = list(product([False, True], repeat=len(atoms)))

    return [dict(zip(atoms, values, strict=False)) for values in truth_values]


def interpretation_is_true(formula, interpretation):
    """
    Auswertung PySMT- Formel unter gegebener Interpretation
    interpretation: Dict[str, bool] — z.B. {"a": True, "b": False}
    """
    substitution = formula.substitute(
        {Symbol(atom): Bool(value) for atom, value in interpretation.items()}
    )
    return substitution.simplify().is_true()


def filter_genuine_splittings(splittings):
    """
    Filtern genuiner konditionaler Syntax-Splittings
    """

    genuine_splittings = []
    for sigma3, sigma1, sigma2, delta1, delta2 in splittings:
        if not delta1.issubset(delta2) and not delta2.issubset(delta1):
            genuine_splittings.append((sigma3, sigma1, sigma2, delta1, delta2))
    return genuine_splittings


def calculate_conditional_syntax_splittings(sigma, delta):
    """
    Berechnen aller konditionalen Syntax-Splittings zu einer gegebenen Wissensbasis und Signatur
    """

    valid_splittings = []

    for sigma3 in powerset_of_sets(sigma):
        sigma_without_sigma3 = sigma.difference(sigma3)

        for sigma1 in powerset_of_sets(sigma_without_sigma3):
            sigma2 = sigma_without_sigma3.difference(sigma1)

            # Vermeide symmetrische Fälle:
            if sorted(sigma1) > sorted(sigma2):
                continue
            delta1, delta2 = set(), set()

            for conditional in delta:
                conditional_atoms = atoms(conditional)  # nur einmal berechnen

                # Prüfe, ob alle Atome des Konditionals in Σ1 ∪ Σ3 liegen
                if conditional_atoms.issubset(sigma1.union(sigma3)):
                    delta1.add(conditional)

                # Prüfe, ob alle Atome des Konditionals in Σ2 ∪ Σ3 liegen
                if conditional_atoms.issubset(sigma2.union(sigma3)):
                    delta2.add(conditional)

            if delta1.union(delta2) == delta:
                valid_splittings.append((sigma3, sigma1, sigma2, delta1, delta2))

    return valid_splittings


def atoms(conditional):
    """
    Liefert die Menge aller atomaren Formeln eines Konditionals
    Funktioniert für Conditional-Objekte und für pysmt-Formeln (FNode)
    """
    if isinstance(conditional, Conditional):
        # Vereinigung aus Antezedenz und Konsequenz
        return atoms(conditional.antecedence).union(atoms(conditional.consequence))
    else:
        # pysmt-Formel
        return {atom.symbol_name() for atom in get_atoms(conditional)}


if __name__ == "__main__":
    main()
