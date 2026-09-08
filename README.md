# Lógica modal en Lean

Formalización en Lean 4 de la lógica modal **K** y de sus teoremas de corrección y completitud respecto a la semántica de Kripke.

Trabajo Fin de Grado del Grado en Matemáticas (Especialización en Ciencias de la Computación), Facultad de Ciencias Matemáticas, Universidad Complutense de Madrid. Septiembre de 2026.

- **Autor:** Jorge Martinena Cepa
- **Tutores:** Ignacio Fábregas y Óscar Martín

## Contenido

- **[`lean/KModalLogic.lean`](lean/KModalLogic.lean)** — la formalización completa, en seis secciones: sintaxis, tautologías clásicas, el sistema axiomático K, semántica de Kripke, corrección (`soundness`) y completitud (`completeness`)
- **[`memoria/main.pdf`](memoria/main.pdf)** — la memoria del trabajo en PDF.

## Compilación

Requiere Lean 4 y Mathlib:

```bash
lake exe cache get
lake build
```
