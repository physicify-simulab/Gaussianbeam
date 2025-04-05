# Interactive Gaussian Beam Simulator

A web-based tool for simulating Gaussian beam propagation through optical systems using the ABCD matrix formalism. This simulator provides accessible, cross-platform simulation capabilities directly within a standard web browser, requiring no installation.

Its core feature is an **interactive canvas** allowing real-time visualization and direct manipulation (drag) of optical elements, offering immediate feedback on system adjustments.

➡️ **[Live Demo](https://physicify-simulab.github.io/Gaussianbeam/)** ⬅️

---

## Key Features

*   **Interactive Canvas:** Visualize beam envelope and wavefronts; drag elements to update propagation in real-time.
*   **Browser-Based & Cross-Platform:** Runs directly in modern web browsers on desktops, tablets, and mobile devices without installation.
*   **Comprehensive Visualization:** Includes the interactive canvas, Plotly plots for beam radius `w(z)` and radius of curvature `R(z)`, and a data table summarizing system parameters.
*   **Element Support:** Simulate common elements (Lenses, Spherical/Flat Mirrors, Dielectric Slabs) and custom components via Generic ABCD matrices.
*   **System Configuration:** Add, remove, and modify elements and initial beam parameters through forms and direct table edits.
*   **Data Export:** Export calculated `w(z)` and `R(z)` data to CSV format.
*   **Open Source:** Freely available under the MIT License.

---

## Screenshots

`![Simulator Screenshot](Screenshot.png)`

---

## Technical Overview

The simulation employs the standard ABCD matrix method for ray transfer analysis. The Gaussian beam state is represented by the complex beam parameter (`q`), which is transformed through the system's cascaded matrices. Beam width `w(z)` and radius of curvature `R(z)` are derived from `q(z)`.

---

## Usage Guide

1.  **Open the Live Demo** (or `index.html` locally).
2.  **Define Initial Beam:** Configure `w₀`, `z₀`, `λ`, `M²`, `n₁`, and plot range in the first row of the "Optical System" table.
3.  **Add Elements:** Use the "Add Optical Element" section to define element type, position, and properties.
4.  **Modify System:** Edit parameters directly in the table or drag elements on the interactive canvas. Use "Remove" buttons in the table as needed.
5.  **Analyze Results:** Observe the updated canvas, plots, and table data.
6.  **Export Data:** Use the CSV export buttons above the plots.

---

## Technical Stack

*   HTML5 / CSS3
*   Vanilla JavaScript (ES6+)
*   [Plotly.js](https://plotly.com/javascript/)

---

## Contributing

Contributions are welcome. Please feel free to submit a Pull Request or open an Issue for bugs or feature suggestions. For significant changes, please open an issue first to discuss.

---

## License

This project is distributed under the [MIT License](LICENSE). See the `LICENSE` file for details.
