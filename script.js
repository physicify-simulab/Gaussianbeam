// --- START OF FILE script.js ---

(function() {
    'use strict'; // Enforce stricter parsing and error handling

    // --- Constants ---
    const PI = Math.PI;
    // const C_LIGHT = 299792458; // Speed of light (m/s) - Currently unused

    // --- Module State (Application State) ---
    let beamParams = {
        w0_um: 100,
        z0_mm: 0,
        lambda_nm: 1064,
        M2: 1.0,
        n: 1.0, // Base refractive index n1
        plotRangeZ_mm: 500
    };
    let opticalElements = []; // { type, position_mm, property: {..}, id }
    let latestPlotData = null; // Cache for canvas and export
    let plotsInitialized = { w: false, r: false };

    // --- DOM Element References ---
    // Initialized in initDOMReferences()
    let elementTypeSelect, elementPositionInput, addElementBtn,
        propertyInputsContainer, propGroups, propInputs, opticsTableBody,
        plotWDiv, plotRDiv, exportWBtn, exportRBtn, showElementsCheck,
        showWaistsCheck, interactiveCanvasElement,
        exportSetupBtn, importSetupBtn, importSetupInput;
    // =========================================================================
    // === UTILITIES ===========================================================
    // =========================================================================

    function debounce(func, wait, immediate) {
        let timeout;
        return function() {
            const context = this, args = arguments;
            const later = function() {
                timeout = null;
                if (!immediate) func.apply(context, args);
            };
            const callNow = immediate && !timeout;
            clearTimeout(timeout);
            timeout = setTimeout(later, wait);
            if (callNow) func.apply(context, args);
        };
    }

    // --- Complex Number Helpers ---
    const complex = (re = 0, im = 0) => ({ re, im });
    const complexAdd = (c1, c2) => complex(c1.re + c2.re, c1.im + c2.im);
    const complexSub = (c1, c2) => complex(c1.re - c2.re, c1.im - c2.im);
    const complexMul = (c1, c2) => complex(c1.re * c2.re - c1.im * c2.im, c1.re * c2.im + c1.im * c2.re);
    const complexConj = (c) => complex(c.re, -c.im);
    const complexMagSq = (c) => c.re * c.re + c.im * c.im;
    const complexDiv = (c1, c2) => {
        const denom = complexMagSq(c2);
        if (denom === 0) return complex(Infinity, Infinity);
        const num = complexMul(c1, complexConj(c2));
        return complex(num.re / denom, num.im / denom);
    };
    const complexReciprocal = (c) => {
        const denom = complexMagSq(c);
        if (denom === 0) return complex(Infinity, Infinity);
        const conj = complexConj(c);
        return complex(conj.re / denom, conj.im / denom);
    };

    // --- Formatting Helpers ---
    function formatElementType(type) {
        return type ? type.replace(/_/g, ' ').replace(/\b\w/g, l => l.toUpperCase()) : "Unknown Type";
    }

    function formatElementProperties(element) {
        const props = element.property;
        if (!props) return 'Error: No properties';
        try {
            switch (element.type) {
                case 'lens': return `f=${props.f_mm}mm`;
                case 'mirror_spherical': return `R=${props.R_mm}mm`;
                case 'mirror_flat': return `---`;
                case 'slab_dielectric': return `n₂/n₁=${props.n_ratio?.toFixed(2)}, W=${props.width_mm}mm`;
                case 'abcd_generic': return `A=${props.A}, B=${props.B_mm}mm, C=${props.C_perm?.toFixed(4)}/mm, D=${props.D}`;
                default: return JSON.stringify(props);
            }
        } catch (e) {
            console.error("Error formatting properties for element:", element, e);
            return "Error: Invalid props";
        }
    }

    function formatTableValue(value, minPrecision = 2, maxPrecision = 4, epsilon = 1e-9) {
        const parsedValue = parseFloat(value);
        if (isNaN(parsedValue)) return '---';
        const zeroStringMinPrecision = (0.0).toFixed(minPrecision);
        const formattedMin = parsedValue.toFixed(minPrecision);
        if ((formattedMin === zeroStringMinPrecision || formattedMin === `-${zeroStringMinPrecision}`) && Math.abs(parsedValue) >= epsilon) {
            return parsedValue.toFixed(maxPrecision);
        } else {
            return formattedMin;
        }
    }

    function formatForCSV(value) {
        if (value === null || value === undefined) return '""';
        if (!isFinite(value)) return value > 0 ? '"Infinity"' : '"-Infinity"';
        if (isNaN(value)) return '"NaN"';
        return value.toFixed(6);
    }

    function downloadFile(filename, content, mimeType = 'text/plain;charset=utf-8;') {
        const blob = new Blob([content], { type: mimeType });
        const link = document.createElement("a");
        if (link.download !== undefined) {
            const url = URL.createObjectURL(blob);
            link.setAttribute("href", url);
            link.setAttribute("download", filename);
            link.style.visibility = 'hidden';
            document.body.appendChild(link);
            link.click();
            document.body.removeChild(link);
            URL.revokeObjectURL(url);
        } else {
            alert("File download not supported by your browser.");
        }
    }

    // =========================================================================
    // === GAUSSIAN BEAM PHYSICS ===============================================
    // =========================================================================

    // This function is not currently used in the simulation path.
    // If it were, M2 handling would need to be considered based on context.
    function calculateQ(w_m, R_m, lambda_m) {
        if (w_m <= 0) return complex(0, Infinity);
        const term2 = lambda_m / (PI * w_m * w_m); // This is 1/zR for an M2=1 beam if lambda_m is physical.
        const R_inv = (isFinite(R_m) && R_m !== 0) ? 1.0 / R_m : 0;
        const q_inv = complex(R_inv, -term2);
        return complexReciprocal(q_inv);
    }

    // Calculates w and R from a q-parameter and a lambda_arg.
    // If q.im is zR_M2 and lambda_arg is lambda_physical_in_medium,
    // then w_m returned is w_actual / sqrt(M2).
    function calculateWR(q, lambda_arg) { // lambda_arg is physical wavelength in medium
        if (complexMagSq(q) === 0) return { w_m: 0, R_m: 0 };
        const q_inv = complexReciprocal(q);
        const R_m = (q_inv.re === 0) ? Infinity : 1.0 / q_inv.re;
        // q.im = zR_M2 (M2-affected Rayleigh range)
        // lambda_arg = lambda_physical_in_medium = lambda_vac / n
        // w_sq_term = -lambda_arg / (PI * q_inv.im)
        // if q is at waist (q.re=0), q_inv.im = -1/q.im
        // w_sq_term = lambda_arg * q.im / PI
        // w_m = sqrt(lambda_arg * q.im / PI) -> this is w_actual / sqrt(M2)
        const w_sq_term = -lambda_arg / (PI * q_inv.im);
        const w_m = q_inv.im !== 0 ? Math.sqrt(Math.abs(w_sq_term)) : Infinity;
        return { w_m, R_m };
    }

    // Calculates zR and theta from actual physical w0_m, lambda_vac, n_medium, and M2.
    function calculateBeamDerivedParams(w0_m_actual, lambda_m_vac, n_medium, M2_factor) {
        if (w0_m_actual <= 0 || !isFinite(w0_m_actual)) return { zR_m: 0, theta_rad: 0 };
        const lambda_in_medium_m = lambda_m_vac / n_medium;
        // zR_M2 = (PI * w0_actual^2) / (lambda_in_medium * M2_factor)
        //       = (PI * w0_actual^2 * n_medium) / (lambda_vac * M2_factor)
        const zR_m = PI * w0_m_actual * w0_m_actual / (lambda_in_medium_m * M2_factor);
        // theta_M2 = (lambda_in_medium * M2_factor) / (PI * w0_actual)
        //          = ( (lambda_vac / n_medium) * M2_factor) / (PI * w0_actual)
        const theta_rad = (lambda_in_medium_m * M2_factor) / (PI * w0_m_actual);
        return { zR_m, theta_rad };
    }

    // Finds new waist parameters (actual physical w0, z_waist_rel, zR_M2, theta_M2) from an incoming q_in.
    // q_in.im is the M2-affected Rayleigh range.
    function findWaistFromQ(q_in, lambda_m_vac, n_medium, M2_factor) {
        const lambda_in_medium_m = lambda_m_vac / n_medium;
        const z_waist_rel_m = -q_in.re; // Distance from current point to new waist
        const q_waist = complex(0, q_in.im); // q-parameter at the new waist (q_waist.im is new zR_M2)

        // calculateWR returns w_calc = w0_actual_new / sqrt(M2_factor)
        const { w_m: w0_calc } = calculateWR(q_waist, lambda_in_medium_m);

        // Correct to get the actual physical waist
        const w0_actual_new_m = w0_calc * Math.sqrt(M2_factor);

        // Calculate derived parameters using the actual physical waist
        const { zR_m, theta_rad } = calculateBeamDerivedParams(w0_actual_new_m, lambda_m_vac, n_medium, M2_factor);
        // Note: zR_m here should be equal to q_in.im, ensuring self-consistency.

        return { w0_m: w0_actual_new_m, z_waist_rel_m, zR_m, theta_rad };
    }

    // =========================================================================
    // === ABCD MATRIX LOGIC ===================================================
    // =========================================================================

    const identityMatrix = () => [[1, 0], [0, 1]];
    const freeSpaceMatrix = (d_m) => [[1, d_m], [0, 1]];
    const thinLensMatrix = (f_m) => f_m === 0 ? identityMatrix() : [[1, 0], [-1 / f_m, 1]];
    const sphericalMirrorMatrix = (R_m) => R_m === 0 ? identityMatrix() : [[1, 0], [-2.0 / R_m, 1]];
    const flatMirrorMatrix = () => identityMatrix();
    const dielectricSlabMatrix = (n1_base, n2_over_n1_ratio, width_m) => {
        // The q-parameter propagation already accounts for base refractive index n1_base.
        // The matrix for a slab embedded in a medium n1, with slab index n2, and thickness W is:
        // A=1, B=W/n_ratio_slab_to_embedding = W / (n2/n1) , C=0, D=1
        // Here, n2_over_n1_ratio is n_slab / n_base_medium.
        if (n2_over_n1_ratio <= 0) {
            console.warn("Invalid n ratio for dielectric slab:", n2_over_n1_ratio);
            return identityMatrix();
        }
        // The effective B for ABCD matrix operating on q (which is defined using lambda_vac/n_base)
        // is physical_width / (n_slab/n_base)
        const B_eff_m = width_m / n2_over_n1_ratio;
        return [[1, B_eff_m], [0, 1]];
    };
    const genericABCDMatrix = (A, B_m, C_per_m, D) => [[A, B_m], [C_per_m, D]];

    function getElementMatrix(element, n1_base) {
        const props = element.property;
        switch (element.type) {
            case 'lens':             return thinLensMatrix(props.f_mm / 1000.0);
            case 'mirror_spherical': return sphericalMirrorMatrix(props.R_mm / 1000.0);
            case 'mirror_flat':      return flatMirrorMatrix();
            // Pass n1_base to slab_dielectric for clarity, though it might not directly use it if n_ratio is n_slab/n_base
            case 'slab_dielectric':  return dielectricSlabMatrix(n1_base, props.n_ratio, props.width_mm / 1000.0);
            case 'abcd_generic':     return genericABCDMatrix(props.A, props.B_mm / 1000.0, props.C_perm * 1000.0, props.D);
            default:
                console.warn("Unknown element type:", element.type);
                return identityMatrix();
        }
    }

    function multiplyMatrices(M1, M2) { // M = M2 * M1
        const A = M2[0][0] * M1[0][0] + M2[0][1] * M1[1][0];
        const B = M2[0][0] * M1[0][1] + M2[0][1] * M1[1][1];
        const C = M2[1][0] * M1[0][0] + M2[1][1] * M1[1][0];
        const D = M2[1][0] * M1[0][1] + M2[1][1] * M1[1][1];
        return [[A, B], [C, D]];
    }

    function transformQ(q_in, M) { // q_out = (A*q_in + B) / (C*q_in + D)
        const A = M[0][0], B = M[0][1], C = M[1][0], D = M[1][1];
        const num = complexAdd(complexMul(complex(A, 0), q_in), complex(B, 0));
        const den = complexAdd(complexMul(complex(C, 0), q_in), complex(D, 0));
        if (complexMagSq(den) < 1e-16) {
            console.warn("ABCD transformation denominator close to zero.", M, q_in);
            return complex(q_in.re > 0 ? Infinity : -Infinity, 0);
        }
        return complexDiv(num, den);
    }

    // =========================================================================
    // === SIMULATION CORE =====================================================
    // =========================================================================

    function runSimulation() {
        //console.log("Running simulation..."); // Log start

        // 1. Get Input Parameters & Convert to SI units (meters)
        const w0_input_m = beamParams.w0_um / 1e6; // This is the actual physical waist
        const z0_m = beamParams.z0_mm / 1000.0;
        const lambda_vac_m = beamParams.lambda_nm / 1e9;
        const M2_factor = beamParams.M2;
        const n1_base_medium_idx = beamParams.n;
        const plot_end_z_m = beamParams.plotRangeZ_mm / 1000.0;
        
        // Effective wavelength in the base medium (physical wavelength)
        const lambda_in_base_medium_m = lambda_vac_m / n1_base_medium_idx;

        // --- Input Validation ---
        if (w0_input_m <= 0 || lambda_vac_m <= 0 || M2_factor < 1.0 || n1_base_medium_idx < 1.0 || !isFinite(z0_m) || !isFinite(plot_end_z_m) || isNaN(w0_input_m) || isNaN(lambda_vac_m) || isNaN(M2_factor) || isNaN(n1_base_medium_idx) || isNaN(z0_m) || isNaN(plot_end_z_m)) {
            console.error("Invalid initial beam parameters:", beamParams);
            handleSimulationError("Invalid Initial Beam Parameters");
            return; // Stop simulation
        }

        try {
            // 2. Sort Elements by Position
            opticalElements.sort((a, b) => a.position_mm - b.position_mm);

            // 3. Initial Beam Setup & Derived Params (using actual physical w0_input_m)
            const { zR_m: initial_zR_M2_m, theta_rad: initial_theta_M2_rad } = calculateBeamDerivedParams(w0_input_m, lambda_vac_m, n1_base_medium_idx, M2_factor);
            const q_at_waist = complex(0, initial_zR_M2_m); // q.im is the M2-affected Rayleigh range

            // 4. Determine Simulation Start/End
            let min_element_pos_m = z0_m;
            if (opticalElements.length > 0 && !isNaN(opticalElements[0].position_mm)) {
                min_element_pos_m = Math.min(min_element_pos_m, opticalElements[0].position_mm / 1000.0);
            }
            // Ensure simulation starts reasonably before the initial waist or first element
            const typical_zR_display = Math.max(initial_zR_M2_m, 0.01); // Avoid zero or negative zR for range calc
            const simulation_start_z_m = Math.min(0, z0_m - typical_zR_display * 2, min_element_pos_m - typical_zR_display * 0.5);
            const simulation_end_z_m = plot_end_z_m;


            // 5. Calculate Initial q
            const dist_from_waist_to_start = simulation_start_z_m - z0_m;
            let q_current = complexAdd(q_at_waist, complex(dist_from_waist_to_start, 0));
            let z_current_m = simulation_start_z_m;

            // 6. Prepare Data Storage
            const tableData = [];
            const plotData = { z: [], w: [], R: [], elementMarkers: [], waistMarkers: [] };
            const N_POINTS_PER_SEGMENT = 100;
            let last_z_plotted_mm = simulation_start_z_m * 1000 - 1;

            // Add initial beam parameters to table
            tableData.push({
                opticType: "Input Beam", position_mm: beamParams.z0_mm, rel_pos_mm: null,
                waist_um: beamParams.w0_um, waist_pos_mm: beamParams.z0_mm, // Displaying input physical waist
                zR_mm: initial_zR_M2_m * 1000.0, theta_mrad: initial_theta_M2_rad * 1000.0, id: 'initial'
            });
            // For waist marker, w is physical waist radius in meters
            plotData.waistMarkers.push({ z: z0_m, w: w0_input_m, label: `Waist 0 (${(z0_m * 1000).toFixed(1)}mm)` });


            // 7. Propagate through System
            let previous_element_pos_m = z0_m; 

            opticalElements.forEach((element, index) => {
                const element_pos_m = element.position_mm / 1000.0;

                if (isNaN(element_pos_m)) {
                    console.warn(`Skipping element ${index + 1} due to invalid position: ${element.position_mm}`);
                    return; 
                }

                const dist_to_element_m = element_pos_m - z_current_m;

                // A. Propagate free space *before* the element
                if (dist_to_element_m > 1e-12) { // Check for significant positive distance
                    for (let i = 1; i <= N_POINTS_PER_SEGMENT; i++) {
                        const z_step_rel = dist_to_element_m * (i / N_POINTS_PER_SEGMENT);
                        const q_step = complexAdd(q_current, complex(z_step_rel, 0));
                        
                        // calculateWR returns w_calc = w_actual_at_z / sqrt(M2_factor)
                        const { w_m: w_calc, R_m } = calculateWR(q_step, lambda_in_base_medium_m);
                        const w_actual_at_z_m = w_calc * Math.sqrt(M2_factor); // Correct to physical radius

                        const z_abs_m = z_current_m + z_step_rel;
                        const z_abs_mm = z_abs_m * 1000.0;

                        if (z_abs_mm > last_z_plotted_mm + 1e-9 && z_abs_m <= simulation_end_z_m + 1e-9) {
                            plotData.z.push(z_abs_mm);
                            plotData.w.push(w_actual_at_z_m * 1e6); // Store physical radius in um
                            plotData.R.push(isFinite(R_m) ? R_m * 1000.0 : (R_m > 0 ? Infinity : -Infinity));
                            last_z_plotted_mm = z_abs_mm;
                        }
                    }
                    q_current = complexAdd(q_current, complex(dist_to_element_m, 0));
                    z_current_m = element_pos_m;
                } else {
                     if (dist_to_element_m < -1e-12) {
                         console.warn(`Simulation jump: Element ${index + 1} at ${element_pos_m * 1000}mm is before current beam position ${z_current_m * 1000}mm. Advancing position.`);
                     }
                     z_current_m = element_pos_m; 
                }

                // B. Apply the element's transformation
                // n1_base_medium_idx is passed for context, e.g. for dielectric slab effective B calculation
                const M_element = getElementMatrix(element, n1_base_medium_idx);
                q_current = transformQ(q_current, M_element);

                // C. Calculate output beam parameters (new physical waist, new zR_M2, new theta_M2)
                const { w0_m: w0_actual_new_m, z_waist_rel_m: z_waist_rel_new_m, zR_m: zR_M2_new_m, theta_rad: theta_M2_new_rad } = findWaistFromQ(q_current, lambda_vac_m, n1_base_medium_idx, M2_factor);
                const waist_abs_pos_m = z_current_m + z_waist_rel_new_m; 

                // D. Add element data to the table
                const rel_pos_mm = (element_pos_m - previous_element_pos_m) * 1000.0;
                tableData.push({
                    opticType: formatElementType(element.type), position_mm: element.position_mm, rel_pos_mm: rel_pos_mm,
                    properties: formatElementProperties(element), 
                    waist_um: w0_actual_new_m * 1e6, // Store physical waist in um
                    waist_pos_mm: waist_abs_pos_m * 1000.0,
                    zR_mm: zR_M2_new_m * 1000.0, theta_mrad: theta_M2_new_rad * 1000.0, id: element.id
                });

                // E. Add markers for plots (element z in m, waist w in m)
                plotData.elementMarkers.push({ z: element_pos_m, label: `${formatElementType(element.type)} ${index + 1}` });
                plotData.waistMarkers.push({ z: waist_abs_pos_m, w: w0_actual_new_m, label: `Waist ${index + 1}` });


                // F. Update position tracker for next relative calculation
                previous_element_pos_m = element_pos_m;
            });

            // 8. Propagate Final Segment
            const final_dist_m = simulation_end_z_m - z_current_m;
            if (final_dist_m > 1e-12) {
                for (let i = 1; i <= N_POINTS_PER_SEGMENT; i++) {
                    const z_step_rel = final_dist_m * (i / N_POINTS_PER_SEGMENT);
                    const q_step = complexAdd(q_current, complex(z_step_rel, 0));
                    
                    // calculateWR returns w_calc = w_actual_at_z / sqrt(M2_factor)
                    const { w_m: w_calc, R_m } = calculateWR(q_step, lambda_in_base_medium_m);
                    const w_actual_at_z_m = w_calc * Math.sqrt(M2_factor); // Correct to physical radius

                    const z_abs_m = z_current_m + z_step_rel;
                    const z_abs_mm = z_abs_m * 1000.0;

                    if (z_abs_mm > last_z_plotted_mm + 1e-9 && z_abs_m <= simulation_end_z_m + 1e-9) {
                        plotData.z.push(z_abs_mm);
                        plotData.w.push(w_actual_at_z_m * 1e6); // Store physical radius in um
                        plotData.R.push(isFinite(R_m) ? R_m * 1000.0 : (R_m > 0 ? Infinity : -Infinity));
                        last_z_plotted_mm = z_abs_mm;
                    }
                }
            }

            // 9. Store and Update UI
            latestPlotData = { ...plotData }; 
            updateTable(tableData);
            updatePlots(plotData);
            if (typeof CanvasController !== 'undefined' && CanvasController.draw) {
                CanvasController.draw(latestPlotData); 
            } else {
                console.warn("CanvasController not ready for drawing.");
            }

        } catch (error) {
            console.error("Error during simulation calculation:", error);
            handleSimulationError(`Calculation Error: ${error.message}`);
        } finally {
            // console.log("Simulation finished."); // Log end
        }
    }

    function handleSimulationError(message) {
        alert(message);
        // Clear plots
        if (plotWDiv && typeof Plotly !== 'undefined') Plotly.purge(plotWDiv);
        if (plotRDiv && typeof Plotly !== 'undefined') Plotly.purge(plotRDiv);
        plotsInitialized.w = false;
        plotsInitialized.r = false;
        // Clear or show error in table
        if (opticsTableBody) {
            opticsTableBody.innerHTML = `<tr><td colspan="9" style="color: red; text-align: center;">Error: ${message}</td></tr>`;
             // Attempt to redraw with current data for user fixing
             try {
                 const currentTableData = [{
                     opticType: "Input Beam", position_mm: beamParams.z0_mm, rel_pos_mm: null,
                     waist_um: beamParams.w0_um, waist_pos_mm: beamParams.z0_mm,
                     zR_mm: null, theta_mrad: null, id: 'initial'
                 }, ...opticalElements.map((el, index) => ({
                     opticType: formatElementType(el.type), position_mm: el.position_mm, rel_pos_mm: '---', 
                     properties: formatElementProperties(el),
                     waist_um: null, waist_pos_mm: null, zR_mm: null, theta_mrad: null, id: el.id
                 }))];
                 updateTable(currentTableData); 
             } catch (e) {
                 console.error("Error trying to redraw table during error handling:", e);
                 opticsTableBody.innerHTML = `<tr><td colspan="9" style="color: red; text-align: center;">Error: ${message}. Failed to redraw table.</td></tr>`;
             }
        }
        // Clear canvas data
        if (typeof CanvasController !== 'undefined' && CanvasController.draw) {
            CanvasController.draw(null); // Clear canvas
        }
        latestPlotData = null;
    }

    // =========================================================================
    // === UI UPDATE FUNCTIONS =================================================
    // =========================================================================

    function updateTable(data) {
        if (!opticsTableBody) return;
        opticsTableBody.innerHTML = ''; // Clear existing rows

        const initialBeamData = data.find(item => item.id === 'initial');
        if (initialBeamData) {
            addTableRow(initialBeamData, 0); // Index 0 for initial beam
        }

        const elementData = data.filter(item => item.id !== 'initial');
        // Ensure elements are sorted by their actual position *before* adding rows
        elementData.sort((a, b) => a.position_mm - b.position_mm);
        elementData.forEach((item, index) => {
            addTableRow(item, index + 1); // Index starts from 1 for elements
        });
    }

    function addTableRow(item, index) {
        if (!opticsTableBody) return;
        const row = opticsTableBody.insertRow();
        row.insertCell().textContent = item.opticType;

        // --- Position Cell (z0 or element position) ---
        const posCell = row.insertCell();
        if (item.id === 'initial') {
            posCell.appendChild(createTableInput('initial', 'z0_mm', item.position_mm, 'any', null, "Position of the initial beam waist (z₀) (mm)."));
        } else {
             const posInput = createTableInput(item.id, 'position_mm', item.position_mm, 'any', null, `Position of this '${formatElementType(item.opticType)}' (mm).`);
             posInput.dataset.index = index; 
             posCell.appendChild(posInput);
        }

        // --- Relative Position Cell ---
        const relPosCell = row.insertCell();
        if (item.id === 'initial') {
            relPosCell.textContent = '---';
        } else {
            const relPosInput = document.createElement('input');
            relPosInput.type = 'number';
            relPosInput.classList.add('rel-pos-input');
            const relPosValue = parseFloat(item.rel_pos_mm);
             if (item.rel_pos_mm !== null && !isNaN(relPosValue)) {
                 const dummyInput = createTableInput('dummy', 'rel_pos_mm', relPosValue, 'any');
                 relPosInput.value = relPosValue.toFixed(dummyInput.precision);
             } else {
                 relPosInput.value = ''; 
             }
            relPosInput.step = 'any';
            relPosInput.dataset.id = item.id;
            relPosInput.dataset.index = index; 
            relPosInput.title = "Distance from the previous element/waist (mm). Edit to update absolute position.";
            relPosInput.addEventListener('change', handleTableRelPosEdit);
            relPosCell.appendChild(relPosInput);
        }

        // --- Properties Cell ---
        const propCell = row.insertCell();
        propCell.dataset.id = item.id;
        propCell.innerHTML = '';
        if (item.id === 'initial') {
            propCell.appendChild(document.createTextNode('λ='));
            propCell.appendChild(createTableInput('initial', 'lambda_nm', beamParams.lambda_nm, 'any', 1, "Wavelength of the light in vacuum.")); 
            propCell.appendChild(document.createTextNode('nm'));
            propCell.appendChild(document.createElement('br'));
            propCell.appendChild(document.createTextNode('M²='));
            propCell.appendChild(createTableInput('initial', 'M2', beamParams.M2, 0.1, 1.0, "Beam quality factor (M² ≥ 1). Represents deviation from ideal Gaussian."));
            propCell.appendChild(document.createTextNode(', n₁='));
            propCell.appendChild(createTableInput('initial', 'n', beamParams.n, 0.01, 1.0, "Refractive index of the base medium (propagates between elements)."));
            propCell.appendChild(document.createElement('br'));
            propCell.appendChild(document.createTextNode('Plot End Z='));
            propCell.appendChild(createTableInput('initial', 'plotRangeZ_mm', beamParams.plotRangeZ_mm, 'any', null, "Max z-position for plots (mm)."));
            propCell.appendChild(document.createTextNode('mm'));
        } else {
            const element = opticalElements.find(el => el.id === item.id);
            if (element && element.property) {
                try {
                    switch (element.type) {
                        case 'lens':
                            propCell.appendChild(document.createTextNode('f='));
                            propCell.appendChild(createTableInput(item.id, 'f_mm', element.property.f_mm, 'any', null, "Focal length (mm). Positive for converging, negative for diverging."));
                            propCell.appendChild(document.createTextNode('mm'));
                            break;
                        case 'mirror_spherical':
                            propCell.appendChild(document.createTextNode('R='));
                            propCell.appendChild(createTableInput(item.id, 'R_mm', element.property.R_mm, 'any', null, "Radius of curvature (mm). R>0 concave (f>0), R<0 convex (f<0)."));
                            propCell.appendChild(document.createTextNode('mm'));
                            break;
                        case 'mirror_flat': propCell.textContent = '---'; break;
                        case 'slab_dielectric':
                            propCell.appendChild(document.createTextNode('n₂/n₁='));
                            propCell.appendChild(createTableInput(item.id, 'n_ratio', element.property.n_ratio, 0.01, 0.01, "Ratio of slab's refractive index (n₂) to surrounding medium's index (n₁)."));
                            propCell.appendChild(document.createTextNode(', W='));
                            propCell.appendChild(createTableInput(item.id, 'width_mm', element.property.width_mm, 0.1, 0, "Physical thickness of the slab (mm)."));
                            propCell.appendChild(document.createTextNode('mm'));
                            break;
                        case 'abcd_generic':
                            propCell.appendChild(document.createTextNode('A='));
                            propCell.appendChild(createTableInput(item.id, 'A', element.property.A, 0.1));
                            propCell.appendChild(document.createTextNode(', B='));
                            propCell.appendChild(createTableInput(item.id, 'B_mm', element.property.B_mm, 'any'));
                            propCell.appendChild(document.createTextNode('mm'));
                            propCell.appendChild(document.createElement('br')); 
                            propCell.appendChild(document.createTextNode('C='));
                            propCell.appendChild(createTableInput(item.id, 'C_perm', element.property.C_perm, 0.0001));
                            propCell.appendChild(document.createTextNode('/mm, D='));
                            propCell.appendChild(createTableInput(item.id, 'D', element.property.D, 0.1));
                            break;
                        default: propCell.textContent = formatElementProperties(element);
                    }
                } catch (e) {
                    console.error("Error creating property input for element:", element, e);
                    propCell.textContent = "Error";
                }
            } else {
                propCell.textContent = item.properties || '---';
                if (!element) console.warn("Could not find element for table row:", item.id);
            }
        }

        // --- Waist (µm) Cell ---
        const waistCell = row.insertCell();
        if (item.id === 'initial') {
            waistCell.appendChild(createTableInput('initial', 'w0_um', item.waist_um, 0.1, 0.1, "Initial beam waist radius (1/e² intensity radius) at z₀"));
        } else {
            waistCell.textContent = formatTableValue(item.waist_um, 1, 4);
        }

        // --- Waist Pos, Rayleigh, Divergence Cells ---
        row.insertCell().textContent = formatTableValue(item.waist_pos_mm, 2, 4);
        row.insertCell().textContent = formatTableValue(item.zR_mm, 2, 4);
        row.insertCell().textContent = formatTableValue(item.theta_mrad, 2, 4);

        // --- Action Cell ---
        const actionCell = row.insertCell();
        if (item.id !== 'initial') {
            const removeBtn = document.createElement('button');
            removeBtn.textContent = 'Remove';
            removeBtn.classList.add('remove-btn');
            removeBtn.dataset.id = item.id;
            removeBtn.addEventListener('click', handleRemoveElement);
            actionCell.appendChild(removeBtn);
        } else {
            actionCell.textContent = '---';
        }
    }

    function createTableInput(id, propertyName, value, step, minValue = null, description = '') {
        const input = document.createElement('input');
        input.type = 'number';
        const allowsDecimals = step === 'any' || (typeof step === 'number' && step < 1 && step > 0);
        let precision;
        switch (propertyName) {
            case 'M2': precision = 1; break;
            case 'n': case 'n_ratio': precision = 2; break;
            case 'C_perm': precision = 4; break;
            case 'w0_um': case 'lambda_nm': precision = 1; break; 
            default: precision = allowsDecimals ? 2 : 0; break;
        }
        input.precision = precision; 

        let parsedValue = parseFloat(value);
        if (isNaN(parsedValue)) {
            if (propertyName === 'M2' || propertyName === 'n') parsedValue = 1.0;
            else if (propertyName === 'lambda_nm') parsedValue = beamParams.lambda_nm || 1064;
            else if (propertyName === 'plotRangeZ_mm') parsedValue = beamParams.plotRangeZ_mm || 500;
            else parsedValue = 0;
        }
        if (minValue !== null && parsedValue < minValue) {
            parsedValue = minValue;
        }

        input.value = parsedValue.toFixed(precision);
        input.step = step === null ? 'any' : String(step); // Ensure step is string for 'any'
        if (minValue !== null) input.min = String(minValue);
        input.dataset.id = id;
        input.dataset.property = propertyName;
        if (description) input.title = description;
        input.addEventListener('change', handleTableEdit);
        return input;
    }

    function updatePlots(plotData) {
        if (!plotWDiv || !plotRDiv || typeof Plotly === 'undefined') return; 

        if (!plotData || !plotData.z || plotData.z.length === 0) {
            Plotly.purge(plotWDiv);
            Plotly.purge(plotRDiv);
            plotsInitialized.w = false;
            plotsInitialized.r = false;
            return;
        }

        const showElements = showElementsCheck ? showElementsCheck.checked : true;
        const showWaists = showWaistsCheck ? showWaistsCheck.checked : true;
        const largeFinite = 1e9; 

        // --- Calculate Full Data Ranges ---
        const allZValues = plotData.z;
        let minZ = allZValues.length > 0 ? Math.min(...allZValues) : (beamParams.z0_mm - 100);
        let maxZ = Math.max(allZValues.length > 0 ? Math.max(...allZValues) : (beamParams.z0_mm + 100), beamParams.plotRangeZ_mm);
        minZ = isNaN(minZ) ? -100 : minZ;
        maxZ = isNaN(maxZ) ? 500 : maxZ;
        if (minZ >= maxZ) maxZ = minZ + 100; // Ensure maxZ > minZ
        const xRangeBuffer = (maxZ - minZ) * 0.05 || 10;
        const fullXRange = [minZ - xRangeBuffer, maxZ + xRangeBuffer];

        const allWValues = plotData.w.filter(isFinite);
        let maxAbsW = allWValues.length > 0 ? Math.max(...allWValues.map(Math.abs)) : (beamParams.w0_um || 100);
        maxAbsW = (maxAbsW <= 0 || isNaN(maxAbsW)) ? 100 : maxAbsW; // Ensure positive, non-NaN maxAbsW
        const wRangeBuffer = maxAbsW * 0.10 || 1;
        const fullWRangeY = [-maxAbsW - wRangeBuffer, maxAbsW + wRangeBuffer];


        const plotR_vals = plotData.R.map(r => (!isFinite(r)) ? (r > 0 ? largeFinite : -largeFinite) : r);
        let minR_calc = plotR_vals.length > 0 ? Math.min(...plotR_vals) : -1000;
        let maxR_calc = plotR_vals.length > 0 ? Math.max(...plotR_vals) : 1000;
        minR_calc = isNaN(minR_calc) ? -1000 : minR_calc;
        maxR_calc = isNaN(maxR_calc) ? 1000 : maxR_calc;
        if (minR_calc >= maxR_calc) maxR_calc = minR_calc + 1000; // Ensure maxR > minR
        
        let rRangeBuffer = (maxR_calc - minR_calc) * 0.10;
        if (Math.abs(minR_calc) >= largeFinite || Math.abs(maxR_calc) >= largeFinite) rRangeBuffer = Math.max(100, Math.abs(maxR_calc - minR_calc) * 0.02);
        if (maxR_calc === minR_calc) rRangeBuffer = Math.max(100, Math.abs(maxR_calc * 0.2)); // Handle case where all R values are the same
        rRangeBuffer = isFinite(rRangeBuffer) ? rRangeBuffer : 100; // Fallback if rRangeBuffer is not finite
        const fullRRangeY = [minR_calc - rRangeBuffer, maxR_calc + rRangeBuffer];


        // --- Determine Plot Ranges (Preserve Zoom) ---
        const targetWRangeX = plotsInitialized.w ? (plotWDiv.layout?.xaxis?.range || fullXRange) : fullXRange;
        const targetWRangeY = plotsInitialized.w ? (plotWDiv.layout?.yaxis?.range || fullWRangeY) : fullWRangeY;
        const targetRRangeX = plotsInitialized.r ? (plotRDiv.layout?.xaxis?.range || targetWRangeX) : targetWRangeX;
        const targetRRangeY = plotsInitialized.r ? (plotRDiv.layout?.yaxis?.range || fullRRangeY) : fullRRangeY;

        // --- Waist Plot ---
        const traceW = { x: plotData.z, y: plotData.w, mode: 'lines', name: 'W', line: { color: 'blue' } };
        const traceW_neg = { x: plotData.z, y: plotData.w.map(w_val => -w_val), mode: 'lines', name: '-W', line: { color: 'blue' }, showlegend: false };
        const layoutW = {
            xaxis: { title: 'z (mm)', range: targetWRangeX, automargin: true, titlefont: { size: 10 } },
            yaxis: { title: 'w (µm)', range: targetWRangeY, automargin: true, titlefont: { size: 10 } },
            margin: { l: 35, r: 10, t: 5, b: 25 }, shapes: [], annotations: [], hovermode: 'x unified', showlegend: false
        };
        if (showElements && plotData.elementMarkers) {
            const yRangeW = layoutW.yaxis.range; // Use y-axis range from the current plot
            plotData.elementMarkers.forEach(m => {
                if (!m || isNaN(m.z)) return; // m.z is in meters
                const xPosMm = m.z * 1000; // Convert to mm for plotting
                 if (xPosMm >= targetWRangeX[0] && xPosMm <= targetWRangeX[1]) { 
                    layoutW.shapes.push({ type: 'line', x0: xPosMm, y0: yRangeW[0], x1: xPosMm, y1: yRangeW[1], line: { color: 'red', width: 1, dash: 'dot' } });
                    layoutW.annotations.push({ x: xPosMm, y: yRangeW[1] * 0.98, text: m.label || '', showarrow: false, xanchor: 'left', yanchor: 'top', font: { size: 8, color: 'red' } });
                 }
            });
        }
        if (showWaists && plotData.waistMarkers) {
            //const xRangeW = layoutW.xaxis.range; // Not needed if yRangeW is used for conditional check
            plotData.waistMarkers.forEach(m => { // m.z and m.w are in meters
                if (!m || isNaN(m.z) || isNaN(m.w)) return;
                const xPosMm = m.z * 1000; // Convert to mm
                 if (xPosMm >= targetWRangeX[0] && xPosMm <= targetWRangeX[1]) { 
                    const wMarkUm = m.w * 1e6; // Convert waist marker w to um
                    layoutW.shapes.push({ type: 'line', x0: xPosMm, y0: -wMarkUm, x1: xPosMm, y1: wMarkUm, line: { color: 'green', width: 1.5, dash: 'solid' } });
                    layoutW.annotations.push({ x: xPosMm, y: 0, text: (m.label || '') + ` (${xPosMm.toFixed(1)}mm)`, showarrow: true, arrowhead: 2, ax: -20, ay: -20, font: { size: 8, color: 'green' } });
                 }
            });
        }
        try { Plotly.react(plotWDiv, [traceW, traceW_neg], layoutW); plotsInitialized.w = true; }
        catch (e) { console.error("Error rendering Waist plot:", e); Plotly.purge(plotWDiv); plotsInitialized.w = false; }


        // --- RoC Plot ---
        const traceR = { x: plotData.z, y: plotR_vals, mode: 'lines', name: 'R', line: { color: 'purple' } };
        const layoutR = {
            xaxis: { title: 'z (mm)', range: targetRRangeX, automargin: true, titlefont: { size: 10 } },
            yaxis: { title: 'R (mm)', range: targetRRangeY, automargin: true, titlefont: { size: 10 } },
            margin: { l: 35, r: 10, t: 5, b: 25 }, shapes: [], annotations: [], hovermode: 'x unified', showlegend: false
        };
        if (showElements && plotData.elementMarkers) {
             const yRangeR = layoutR.yaxis.range; // Use y-axis range from current plot
             plotData.elementMarkers.forEach(m => {
                 if (!m || isNaN(m.z)) return; // m.z is in meters
                 const xPosMm = m.z * 1000; // Convert to mm
                  if (xPosMm >= targetRRangeX[0] && xPosMm <= targetRRangeX[1]) { 
                     layoutR.shapes.push({ type: 'line', x0: xPosMm, y0: yRangeR[0], x1: xPosMm, y1: yRangeR[1], line: { color: 'red', width: 1, dash: 'dot' } });
                     // Annotations for RoC plot might be too busy, often omitted
                  }
             });
         }
        try { Plotly.react(plotRDiv, [traceR], layoutR); plotsInitialized.r = true; }
        catch (e) { console.error("Error rendering RoC plot:", e); Plotly.purge(plotRDiv); plotsInitialized.r = false; }
    }

    // =========================================================================
    // === CSV EXPORT ==========================================================
    // =========================================================================

    function downloadCSV(filename, dataRows) {
        if (!dataRows || dataRows.length <= 1) { 
            alert("No data available to export."); return;
        }
        const csvContent = dataRows.map(row => row.join(",")).join("\n");
        const blob = new Blob([csvContent], { type: 'text/csv;charset=utf-8;' });
        const link = document.createElement("a");
        if (link.download !== undefined) {
            const url = URL.createObjectURL(blob);
            link.setAttribute("href", url);
            link.setAttribute("download", filename);
            link.style.visibility = 'hidden';
            document.body.appendChild(link);
            link.click();
            document.body.removeChild(link);
            URL.revokeObjectURL(url);
        } else {
            alert("CSV download not supported by your browser.");
        }
    }

    function handleExportW() {
        if (!latestPlotData || !latestPlotData.z || !latestPlotData.w) { alert("Simulation data not available yet."); return; }
        const rows = [["z_mm", "w_um"]];
        for (let i = 0; i < latestPlotData.z.length; i++) {
            if (latestPlotData.z[i] !== undefined && latestPlotData.w[i] !== undefined) {
                rows.push([formatForCSV(latestPlotData.z[i]), formatForCSV(latestPlotData.w[i])]);
            }
        }
        downloadCSV("beam_waist_data.csv", rows);
    }

    function handleExportR() {
        if (!latestPlotData || !latestPlotData.z || !latestPlotData.R) { alert("Simulation data not available yet."); return; }
        const rows = [["z_mm", "R_mm"]];
        for (let i = 0; i < latestPlotData.z.length; i++) {
            if (latestPlotData.z[i] !== undefined && latestPlotData.R[i] !== undefined) {
                rows.push([formatForCSV(latestPlotData.z[i]), formatForCSV(latestPlotData.R[i])]);
            }
        }
        downloadCSV("beam_roc_data.csv", rows);
    }

    // =========================================================================
    // === XML EXPORT/IMPORT ===================================================
    // =========================================================================

    function handleExportSetup() {
        console.log("Exporting setup...");
        try {
            const xmlDoc = document.implementation.createDocument(null, "opticalSystem", null);
            const root = xmlDoc.documentElement;

            const beamNode = xmlDoc.createElement("beamParameters");
            for (const key in beamParams) {
                if (Object.hasOwnProperty.call(beamParams, key)) {
                    beamNode.setAttribute(key, String(beamParams[key]));
                }
            }
            root.appendChild(beamNode);

            const elementsNode = xmlDoc.createElement("elements");
            opticalElements.forEach(element => {
                const elementNode = xmlDoc.createElement("element");
                elementNode.setAttribute("type", element.type);
                elementNode.setAttribute("position_mm", String(element.position_mm));
                // ID is not saved, it's recreated on import for uniqueness.

                if (element.property && Object.keys(element.property).length > 0) {
                    const propertyNode = xmlDoc.createElement("property");
                    for (const propKey in element.property) {
                        if (Object.hasOwnProperty.call(element.property, propKey)) {
                             propertyNode.setAttribute(propKey, String(element.property[propKey]));
                        }
                    }
                    elementNode.appendChild(propertyNode);
                }
                elementsNode.appendChild(elementNode);
            });
            root.appendChild(elementsNode);

            const serializer = new XMLSerializer();
            const xmlString = '<?xml version="1.0" encoding="UTF-8"?>\n' + serializer.serializeToString(xmlDoc);

            downloadFile("gaussian_beam_setup.xml", xmlString, 'application/xml;charset=utf-8;');
            console.log("Setup exported successfully.");

        } catch (error) {
            console.error("Error exporting setup:", error);
            alert("Error exporting setup. See console for details.");
        }
    }

    function handleImportSetupTrigger() {
        if (importSetupInput) {
            importSetupInput.click();
        } else {
            console.error("Import file input not found.");
            alert("Import feature error: File input element missing.");
        }
    }

    function handleImportSetupFileSelect(event) {
        const file = event.target.files[0];
        if (!file) {
            console.log("No file selected for import.");
            return;
        }
        if (!file.name.toLowerCase().endsWith('.xml')) {
            alert("Invalid file type. Please select an XML file (.xml).");
            event.target.value = null;
            return;
        }

        console.log("Importing setup from:", file.name);
        const reader = new FileReader();

        reader.onload = function(e) {
            const xmlString = e.target.result;
            try {
                const parser = new DOMParser();
                const xmlDoc = parser.parseFromString(xmlString, "application/xml");

                const parserError = xmlDoc.getElementsByTagName("parsererror");
                 if (parserError.length > 0) {
                     console.error("XML Parsing Error:", parserError[0].textContent);
                     throw new Error("Failed to parse XML file. Check format and validity.");
                 }

                const root = xmlDoc.documentElement;
                if (!root || root.tagName !== 'opticalSystem') {
                    throw new Error("Invalid XML format: Missing <opticalSystem> root element.");
                }

                const beamNode = root.querySelector("beamParameters");
                if (!beamNode) {
                    throw new Error("Invalid XML format: Missing <beamParameters> element.");
                }
                const importedBeamParams = {}; 
                const expectedBeamParams = ['w0_um', 'z0_mm', 'lambda_nm', 'M2', 'n', 'plotRangeZ_mm'];
                let missingBeamParam = null;
                for (const key of expectedBeamParams) {
                    const value = beamNode.getAttribute(key);
                    if (value === null) {
                         missingBeamParam = key;
                         break;
                    }
                    const numValue = parseFloat(value);
                    if (isNaN(numValue)) {
                        throw new Error(`Invalid value for beam parameter '${key}': "${value}". Must be a number.`);
                    }
                    let clampedValue = numValue;
                    switch (key) {
                        case 'w0_um':     clampedValue = Math.max(0.1, numValue); break;
                        case 'lambda_nm': clampedValue = Math.max(1, numValue); break;
                        case 'M2':        clampedValue = Math.max(1.0, numValue); break;
                        case 'n':         clampedValue = Math.max(1.0, numValue); break;
                    }
                    if (clampedValue !== numValue) console.warn(`Imported beam param ${key} value clamped from ${numValue} to ${clampedValue}`);
                    importedBeamParams[key] = clampedValue;
                }
                 if (missingBeamParam) {
                      throw new Error(`Invalid XML format: Missing required beam parameter attribute '${missingBeamParam}'.`);
                 }

                const elementsNode = root.querySelector("elements");
                if (!elementsNode) {
                    throw new Error("Invalid XML format: Missing <elements> element.");
                }
                const importedElements = []; 
                const elementNodes = elementsNode.querySelectorAll("element");

                elementNodes.forEach((elNode, index) => {
                    const type = elNode.getAttribute("type");
                    const posStr = elNode.getAttribute("position_mm");

                    if (!type) throw new Error(`Element ${index + 1}: Missing 'type' attribute.`);
                    if (posStr === null) throw new Error(`Element ${index + 1} (type ${type}): Missing 'position_mm' attribute.`);

                    const position_mm = parseFloat(posStr);
                    if (isNaN(position_mm)) throw new Error(`Element ${index + 1} (type ${type}): Invalid 'position_mm' value "${posStr}".`);

                    const element = {
                        type: type,
                        position_mm: position_mm,
                        property: {},
                        id: Date.now().toString() + Math.random().toString(36).substring(2, 9) + `_import${index}`
                    };

                    const propNode = elNode.querySelector("property");
                    const expectedProps = getExpectedPropertiesForType(type);

                    if (expectedProps.length > 0) {
                        if (!propNode) throw new Error(`Element ${index + 1} (type ${type}): Missing <property> tag, but properties are expected.`);
                        expectedProps.forEach(propKey => {
                            const propValueStr = propNode.getAttribute(propKey);
                            if (propValueStr === null) throw new Error(`Element ${index + 1} (type ${type}): Missing property attribute '${propKey}'.`);
                            const propValue = parseFloat(propValueStr);
                            if (isNaN(propValue)) throw new Error(`Element ${index + 1} (type ${type}): Invalid value for property '${propKey}': "${propValueStr}".`);
                            let clampedPropValue = propValue;
                            switch (propKey) {
                                case 'n_ratio':  clampedPropValue = Math.max(0.01, propValue); break;
                                case 'width_mm': clampedPropValue = Math.max(0, propValue); break;
                            }
                            if (clampedPropValue !== propValue) console.warn(`Imported element ${index + 1} property ${propKey} value clamped from ${propValue} to ${clampedPropValue}`);
                            element.property[propKey] = clampedPropValue;
                        });
                    } else if (propNode) {
                         console.warn(`Element ${index + 1} (type ${type}): Found <property> tag but none are expected for this type. Ignoring properties.`);
                    }
                    importedElements.push(element); 
                });

                console.log("Updating beamParams object in place...");
                for (const key in importedBeamParams) {
                    if (Object.hasOwnProperty.call(importedBeamParams, key)) {
                        beamParams[key] = importedBeamParams[key];
                    }
                }
                // Clear any old keys in beamParams that weren't in the import, if desired,
                // but generally overwriting is sufficient for the defined structure.

                console.log("Updating opticalElements array in place...");
                opticalElements.length = 0; 
                opticalElements.push(...importedElements);
                
                console.log("Setup imported successfully (in-place update).");
                runSimulation(); 

            } catch (error) {
                console.error("Error importing setup:", error);
                alert(`Error importing setup: ${error.message}\nPlease ensure the XML file is valid and has the correct structure.`);
            } finally {
                event.target.value = null;
            }
        };

        reader.onerror = function(e) {
            console.error("Error reading file:", e);
            alert("Error reading the selected file.");
            event.target.value = null; 
        };

        reader.readAsText(file);
    }


    // Helper to get expected property keys for validation
    function getExpectedPropertiesForType(type) {
        switch (type) {
            case 'lens':             return ['f_mm'];
            case 'mirror_spherical': return ['R_mm'];
            case 'mirror_flat':      return [];
            case 'slab_dielectric':  return ['n_ratio', 'width_mm'];
            case 'abcd_generic':     return ['A', 'B_mm', 'C_perm', 'D'];
            default:
                console.warn("Validation check: Unknown element type encountered during import:", type);
                return []; 
        }
    }

    // =========================================================================
    // === EVENT HANDLERS ======================================================
    // =========================================================================

    function handlePlotOptionChange() {
        runSimulation(); 
    }

    function handleElementTypeChange() {
        const selectedType = elementTypeSelect.value;
        Object.values(propGroups).forEach(group => { if (group) group.style.display = 'none'; });
        if (propGroups[selectedType]) {
            propGroups[selectedType].style.display = 'inline-flex'; 
        }
    }

    function handleAddElement() {
        const type = elementTypeSelect.value;
        const position_mm = parseFloat(elementPositionInput.value);
        let properties = {};
        let isValid = !isNaN(position_mm);

        try { 
            switch(type) {
                case 'lens':
                    properties.f_mm = parseFloat(propInputs.f.value);
                    isValid = isValid && !isNaN(properties.f_mm);
                    break;
                case 'mirror_spherical':
                    properties.R_mm = parseFloat(propInputs.r.value);
                    isValid = isValid && !isNaN(properties.R_mm);
                    break;
                case 'mirror_flat': break;
                case 'slab_dielectric':
                    properties.n_ratio = parseFloat(propInputs.nratio.value);
                    properties.width_mm = parseFloat(propInputs.widthSlab.value);
                    isValid = isValid && !isNaN(properties.n_ratio) && properties.n_ratio > 0 && !isNaN(properties.width_mm) && properties.width_mm >= 0;
                    break;
                case 'abcd_generic':
                    properties.A = parseFloat(propInputs.A.value);
                    properties.B_mm = parseFloat(propInputs.B.value);
                    properties.C_perm = parseFloat(propInputs.C.value);
                    properties.D = parseFloat(propInputs.D.value);
                    isValid = isValid && !isNaN(properties.A) && !isNaN(properties.B_mm) && !isNaN(properties.C_perm) && !isNaN(properties.D);
                    break;
                default: isValid = false;
            }
        } catch (e) {
             console.error("Error parsing properties for adding element:", e);
             isValid = false;
        }

        if (!isValid) {
            alert("Please enter valid numbers for position and all required properties.");
            return;
        }

        opticalElements.push({
            type: type, position_mm: position_mm, property: properties,
            id: Date.now().toString() + Math.random().toString(36).substring(2, 9)
        });
        runSimulation();
    }

    function handleRemoveElement(event) {
        const idToRemove = event.target.dataset.id;
        const indexToRemove = opticalElements.findIndex(el => el.id === idToRemove);
        if (indexToRemove > -1) {
            opticalElements.splice(indexToRemove, 1);
            runSimulation();
        } else {
            console.warn("Element to remove not found:", idToRemove);
        }
    }

    function handleTableEdit(event) {
        const target = event.target;
        const id = target.dataset.id;
        const propertyToChange = target.dataset.property;
        const rawValue = target.value;
        let newValue = parseFloat(rawValue);

        if (isNaN(newValue)) {
            alert(`Invalid value "${rawValue}" entered for ${propertyToChange}. Please enter a valid number.`);
            resetInputValueOnError(target, id, propertyToChange);
            return;
        }

        let clampedValue = newValue;
        switch (propertyToChange) {
            case 'w0_um':     clampedValue = Math.max(0.1, newValue); break;
            case 'lambda_nm': clampedValue = Math.max(1, newValue); break;
            case 'M2':        clampedValue = Math.max(1.0, newValue); break;
            case 'n':         clampedValue = Math.max(1.0, newValue); break;
            case 'n_ratio':   clampedValue = Math.max(0.01, newValue); break;
            case 'width_mm':  clampedValue = Math.max(0, newValue); break;
        }

        if (clampedValue !== newValue) {
            console.warn(`Value for ${propertyToChange} clamped from ${newValue} to ${clampedValue}`);
            const dummyInput = createTableInput('dummy', propertyToChange, clampedValue, target.step || 'any');
            target.value = clampedValue.toFixed(dummyInput.precision);
            newValue = clampedValue; 
        }

        if (id === 'initial') {
            if (propertyToChange in beamParams) {
                beamParams[propertyToChange] = newValue;
            } else {
                console.warn("Attempted to edit unknown beam parameter:", propertyToChange); return;
            }
        } else {
            const elementIndex = opticalElements.findIndex(el => el.id === id);
            if (elementIndex > -1) {
                if (propertyToChange === 'position_mm') {
                    opticalElements[elementIndex].position_mm = newValue;
                } else if (opticalElements[elementIndex].property) {
                    opticalElements[elementIndex].property[propertyToChange] = newValue;
                } else if (opticalElements[elementIndex].type !== 'mirror_flat'){ 
                     console.warn(`Property object for element ${id} missing, creating it.`);
                     opticalElements[elementIndex].property = { [propertyToChange]: newValue };
                } else {
                     console.warn(`Cannot set property '${propertyToChange}' on flat mirror ${id}.`); return; 
                }
            } else {
                console.warn("Element not found for edit:", id); return;
            }
        }
        runSimulation(); 
    }

    function handleTableRelPosEdit(event) {
        const target = event.target;
        const id = target.dataset.id;
        const rawValue = target.value;
        const newRelPos = parseFloat(rawValue);

        if (isNaN(newRelPos)) {
            alert(`Invalid relative position "${rawValue}". Please enter a valid number.`);
            resetInputValueOnError(target, id, 'rel_pos_mm');
            return;
        }

        const elementStorageIndex = opticalElements.findIndex(el => el.id === id);
        if (elementStorageIndex === -1) {
            console.error("Could not find element to update relative position:", id);
            runSimulation(); 
            return;
        }

        const sortedPositions = [
            { id: 'initial', position_mm: beamParams.z0_mm },
            ...opticalElements.map(el => ({ id: el.id, position_mm: el.position_mm }))
        ].sort((a, b) => a.position_mm - b.position_mm);

        const currentSortedIndex = sortedPositions.findIndex(el => el.id === id);

        if (currentSortedIndex < 1) { 
            console.error("Cannot set relative position for the first element in the sorted list.");
            resetInputValueOnError(target, id, 'rel_pos_mm'); 
            return;
        }

        const prevElementAbsPos = sortedPositions[currentSortedIndex - 1].position_mm;

        if (isNaN(prevElementAbsPos)) {
            console.error("Previous element position is invalid for relative calculation.");
            runSimulation(); 
            return;
        }

        const newAbsPos = prevElementAbsPos + newRelPos;
        opticalElements[elementStorageIndex].position_mm = newAbsPos;
        console.log(`Updated pos of ${id} via rel pos: Prev Abs=${formatTableValue(prevElementAbsPos,2,4)} + Rel=${formatTableValue(newRelPos,2,4)} = New Abs=${formatTableValue(newAbsPos,2,4)}`);
        runSimulation();
    }

    function resetInputValueOnError(targetInputElement, elementId, propertyName) {
         let originalValue;
         if (elementId === 'initial') {
             originalValue = beamParams[propertyName];
         } else {
              const element = opticalElements.find(el => el.id === elementId);
              if (element) {
                  if (propertyName === 'position_mm') {
                      originalValue = element.position_mm;
                  } else if (propertyName === 'rel_pos_mm') {
                      const sortedPositions = [
                          { id: 'initial', position_mm: beamParams.z0_mm },
                          ...opticalElements.map(el => ({ id: el.id, position_mm: el.position_mm }))
                      ].sort((a, b) => a.position_mm - b.position_mm);
                      const currentSortedIndex = sortedPositions.findIndex(el => el.id === elementId);
                      if (currentSortedIndex > 0 && !isNaN(sortedPositions[currentSortedIndex - 1].position_mm) && !isNaN(element.position_mm)) {
                          originalValue = element.position_mm - sortedPositions[currentSortedIndex - 1].position_mm;
                      } else {
                          originalValue = null; 
                      }
                  } else {
                       originalValue = element.property?.[propertyName];
                  }
              }
         }

         if (originalValue !== undefined && originalValue !== null && !isNaN(originalValue)) {
              const dummyInput = createTableInput('dummy', propertyName, originalValue, targetInputElement.step || 'any');
              targetInputElement.value = parseFloat(originalValue).toFixed(dummyInput.precision);
         } else if (propertyName === 'rel_pos_mm' && originalValue === null) {
              targetInputElement.value = ''; 
         } else {
              targetInputElement.value = '';
              console.warn(`Could not find original valid value for ${propertyName} of ${elementId} to reset input.`);
         }
    }


    const handleResize = debounce(() => {
        console.log("Window resized, updating plots and canvas...");
        if (plotsInitialized.w && plotWDiv?.layout && typeof Plotly !== 'undefined') {
             try { Plotly.Plots.resize(plotWDiv); } catch (e) { console.warn("Could not resize Plot W:", e); }
        }
        if (plotsInitialized.r && plotRDiv?.layout && typeof Plotly !== 'undefined') {
             try { Plotly.Plots.resize(plotRDiv); } catch (e) { console.warn("Could not resize Plot R:", e); }
        }
        if (typeof CanvasController !== 'undefined' && CanvasController.handleResize) {
            CanvasController.handleResize();
        }
    }, 250);

    // =========================================================================
    // === INITIALIZATION ======================================================
    // =========================================================================

    function initDOMReferences() {
        elementTypeSelect = document.getElementById('elementType');
        elementPositionInput = document.getElementById('elementPosition');
        addElementBtn = document.getElementById('addElementBtn');
        propertyInputsContainer = document.getElementById('propertyInputsContainer');
        opticsTableBody = document.getElementById('opticsTableBody');
        plotWDiv = document.getElementById('plotW');
        plotRDiv = document.getElementById('plotR');
        exportWBtn = document.getElementById('exportWBtn');
        exportRBtn = document.getElementById('exportRBtn');
        showElementsCheck = document.getElementById('showElementsCheck');
        showWaistsCheck = document.getElementById('showWaistsCheck');
        interactiveCanvasElement = document.getElementById('interactiveCanvas');
        exportSetupBtn = document.getElementById('exportSetupBtn');
        importSetupBtn = document.getElementById('importSetupBtn');
        importSetupInput = document.getElementById('importSetupInput');

        propGroups = {
            lens: document.getElementById('props-lens'),
            mirror_spherical: document.getElementById('props-mirror_spherical'),
            mirror_flat: document.getElementById('props-mirror_flat'),
            slab_dielectric: document.getElementById('props-slab_dielectric'),
            abcd_generic: document.getElementById('props-abcd_generic'),
        };
        propInputs = {
            f: document.getElementById('prop-f'),
            r: document.getElementById('prop-r'),
            nratio: document.getElementById('prop-nratio'),
            widthSlab: document.getElementById('prop-width-slab'),
            A: document.getElementById('prop-A'), B: document.getElementById('prop-B'),
            C: document.getElementById('prop-C'), D: document.getElementById('prop-D'),
        };
         if (!elementTypeSelect || !addElementBtn || !opticsTableBody || !plotWDiv || !interactiveCanvasElement || !exportSetupBtn || !importSetupBtn || !importSetupInput) { 
            console.error("FATAL: Could not find essential DOM elements. Aborting initialization.");
            alert("Error initializing the page. Some elements are missing. Check the console (F12).");
            return false; 
        }
        return true; 
   }

   function setupEventListeners() {
       if (elementTypeSelect) elementTypeSelect.addEventListener('change', handleElementTypeChange);
       if (addElementBtn) addElementBtn.addEventListener('click', handleAddElement);

       if (showElementsCheck) showElementsCheck.addEventListener('change', handlePlotOptionChange);
       if (showWaistsCheck) showWaistsCheck.addEventListener('change', handlePlotOptionChange);

       if (exportWBtn) exportWBtn.addEventListener('click', handleExportW);
       if (exportRBtn) exportRBtn.addEventListener('click', handleExportR);
       if (exportSetupBtn) exportSetupBtn.addEventListener('click', handleExportSetup); 

       if (importSetupBtn) importSetupBtn.addEventListener('click', handleImportSetupTrigger); 
       if (importSetupInput) importSetupInput.addEventListener('change', handleImportSetupFileSelect); 

       window.addEventListener('resize', handleResize);
   }

   function initialize() {
       console.log("Initializing Simulator...");
       if (!initDOMReferences()) return; 

       handleElementTypeChange();

       if (typeof CanvasController !== 'undefined' && CanvasController.init) {
           CanvasController.init(interactiveCanvasElement, opticalElements, beamParams, runSimulation);
       } else {
           console.error("CanvasController is not loaded or defined! Interactive canvas will not work.");
           if(interactiveCanvasElement) interactiveCanvasElement.style.display = 'none';
       }

       setupEventListeners();

       try {
           runSimulation();
       } catch (e) {
           console.error("Error during initial simulation run:", e);
       }

       setTimeout(handleResize, 150);
       console.log("Initialization complete.");
   }

   if (document.readyState === 'loading') {
       document.addEventListener('DOMContentLoaded', initialize);
   } else {
       initialize();
   }

})(); 

// --- END OF FILE script.js ---
