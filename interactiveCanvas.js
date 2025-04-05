/* eslint-disable no-undef */ // For Math symbols like PI
/* eslint-disable no-unused-vars */ // To allow unused vars like in event handlers
// interactiveCanvas.js

/**
 * @typedef {import('./pathSimulator.js').OpticalElement} OpticalElement
 * @typedef {import('./pathSimulator.js').BeamParams} BeamParams
 * @typedef {import('./pathSimulator.js').SimulationResult} SimulationResult
 */

// Use an IIFE (Immediately Invoked Function Expression) to create a local scope
// and avoid polluting the global namespace.
const CanvasController = (() => {
    // --- Constants ---
    const DRAW_CONSTANTS = {
        ELEMENT_HIT_TOLERANCE_PX: 20, // Pixels +/- for interaction
        WAVEFRONT_SPACING_MM: 10,   // How often to draw a wavefront
        MAX_WAVEFRONTS: 100,        // Limit number of wavefronts
        LENS_SYMBOL_WIDTH_PX: 8,    // Visual width of lens symbols
        ELEMENT_SYMBOL_HEIGHT_FACTOR: 0.75, // Fraction of plot height for element symbols
        MIN_PLOT_HEIGHT_FACTOR_W0: 0.3, // Minimum plot height relative to w0
        MIN_PLOT_HEIGHT_ABS_UM: 10,     // Absolute minimum plot height in um
        PLOT_MAX_W_MARGIN_FACTOR: 1.15, // Multiplier for max beam size for y-axis scaling
        FONT_AXIS_LABEL: '11px sans-serif',
        FONT_AXIS_TITLE: 'bold 11px sans-serif',
        FONT_ELEMENT_LABEL: '10px sans-serif',
        COLOR_WAVEFRONT: 'rgba(100, 0, 100, 0.6)', // Darker purple wavefronts
        COLOR_AXIS: '#000000',                   // Black axes
        COLOR_TICK_LABEL: '#000000',             // Black labels
        COLOR_ELEMENT_STROKE: '#cc0000',           // Brighter red elements outline (#cc0000)
        COLOR_ELEMENT_FILL: 'rgba(204, 0, 0, 0.5)', // Semi-transparent red fill
        COLOR_ELEMENT_LABEL: '#cc0000',           // Opaque red label text
        COLOR_BEAM_STROKE: 'rgba(0, 0, 150, 0.6)', // Darker blue outline
        COLOR_BACKGROUND: '#ffffff',               // White background
        COLOR_PLOT_BORDER: '#bbbbbb',              // Grey border
        COLOR_WAITING_TEXT: '#555555',            // Darker Grey text
        NUM_X_TICKS: 5,
        NUM_Y_TICKS: 5,
        GAUSSIAN_FILL_STEPS: 10,                  // Number of color stops in gradient fill
        GAUSSIAN_FILL_SLICE_WIDTH_PX: 2,         // Width of vertical slices for fill
        DRAG_UPDATE_MIN_PIXEL_CHANGE: 0.5,       // Min pixels moved before update trigger
        TARGET_ASPECT_RATIO: 2.5,
        MIN_CANVAS_WIDTH: 200,
        MAX_CANVAS_WIDTH: 1600,
        MIN_CANVAS_HEIGHT: 100,
        MARGIN_TOP: 15,
        MARGIN_RIGHT: 15,
        MARGIN_BOTTOM: 45, // Increased for x-label
        MARGIN_LEFT: 35,   // Reduced for y-title rotation space
    };

    // --- Module State ---
    let canvas = null;
    let ctx = null;
    /** @type {OpticalElement[] | null} */
    let opticalElementsRef = null; // Reference to the main opticalElements array
    /** @type {BeamParams | null} */
    let beamParamsRef = null;      // Reference to beam parameters
    /** @type {Function | null} */
    let simulationUpdateCallback = null; // Function to call when sim needs update
    /** @type {SimulationResult | null} */
    let simulationDataCache = null; // Local cache of simulation { z, w, R } data

    // Drag state
    let draggedElement = null;
    let isDragging = false;

    // --- Private Helper Functions ---

    // --- Event Helpers ---
    /** Gets Mouse/Touch position relative to canvas */
    function getEventPos(evt) {
        if (!canvas) return { x: 0, y: 0 };
        const rect = canvas.getBoundingClientRect();
        let clientX, clientY;

        if (evt.touches && evt.touches.length > 0) {
            clientX = evt.touches[0].clientX;
            clientY = evt.touches[0].clientY;
        } else if (evt.changedTouches && evt.changedTouches.length > 0) {
            clientX = evt.changedTouches[0].clientX;
            clientY = evt.changedTouches[0].clientY;
        } else {
            clientX = evt.clientX;
            clientY = evt.clientY;
        }
        return { x: clientX - rect.left, y: clientY - rect.top };
    }

    /** Finds the topmost optical element at a given canvas position */
    function findElementAtPos(pos) {
        if (!opticalElementsRef || !pos) return null;
        // Iterate backwards (top elements drawn last)
        for (let i = opticalElementsRef.length - 1; i >= 0; i--) {
            const element = opticalElementsRef[i];
            if (element.canvasRect &&
                pos.x >= element.canvasRect.x &&
                pos.x <= element.canvasRect.x + element.canvasRect.w &&
                pos.y >= element.canvasRect.y &&
                pos.y <= element.canvasRect.y + element.canvasRect.h)
            {
                return element;
            }
        }
        return null; // No element found
    }

    // --- Coordinate and Layout Helpers ---
    /** Calculates drawing parameters based on current canvas size and simulation data range. */
    function getDrawParams() {
        if (!simulationDataCache?.z?.length || !canvas || !beamParamsRef) {
            return null;
        }

        const canvasW = canvas.width;
        const canvasH = canvas.height;
        const margin = {
            top: DRAW_CONSTANTS.MARGIN_TOP,
            right: DRAW_CONSTANTS.MARGIN_RIGHT,
            bottom: DRAW_CONSTANTS.MARGIN_BOTTOM,
            left: DRAW_CONSTANTS.MARGIN_LEFT
        };
        const plotWidth = canvasW - margin.left - margin.right;
        const plotHeight = canvasH - margin.top - margin.bottom;

        if (plotWidth <= 0 || plotHeight <= 0) return null; // Invalid dimensions

        const zMin_mm = simulationDataCache.z[0];
        const zMax_mm = simulationDataCache.z[simulationDataCache.z.length - 1];
        const zRange_mm = zMax_mm - zMin_mm;

        const validW = simulationDataCache.w.filter(isFinite);
        const w0_fallback = beamParamsRef?.w0_um || 100;
        const calculatedMaxW_um = validW.length > 0 ? Math.max(...validW) : w0_fallback;
        const minPlotW_um = Math.max(
            DRAW_CONSTANTS.MIN_PLOT_HEIGHT_ABS_UM,
            w0_fallback * DRAW_CONSTANTS.MIN_PLOT_HEIGHT_FACTOR_W0
        );
        const plotMaxW_um = Math.max(calculatedMaxW_um * DRAW_CONSTANTS.PLOT_MAX_W_MARGIN_FACTOR, minPlotW_um);

        const scaleX = (zRange_mm > 1e-9) ? plotWidth / zRange_mm : 0; // px per mm
        const scaleY = (plotMaxW_um > 1e-9) ? plotHeight / (2 * plotMaxW_um) : 0; // px per um

        return {
            canvasW, canvasH, margin, plotWidth, plotHeight,
            zMin_mm, zMax_mm, zRange_mm, plotMaxW_um,
            scaleX, scaleY, // Scales for convenience
            yCenter: margin.top + plotHeight / 2,
        };
    }

    /** Convert Z position (mm) to canvas X coordinate (px) */
    function zToX(z_mm, params) {
        if (!params || !isFinite(z_mm)) return NaN;
        // Use scaleX for efficiency, handle zero range case
        if (params.scaleX === 0) return params.margin.left + params.plotWidth / 2;
        return params.margin.left + (z_mm - params.zMin_mm) * params.scaleX;
    }

    /** Convert Beam Radius W (um) to canvas Y coordinate (px) */
    function wToY(w_um, params) {
        if (!params || !isFinite(w_um)) return NaN;
        // Use scaleY for efficiency, handles zero plotMaxW case implicitly (scaleY=0)
        return params.yCenter - w_um * params.scaleY;
    }

    /** Convert canvas X coordinate (px) to Z position (mm) */
    function xToZ(x_px, params) {
        if (!params || !isFinite(x_px)) return NaN;
        if (params.plotWidth === 0) return params.zMin_mm; // Avoid division by zero
        const relativeX = Math.max(0, Math.min(params.plotWidth, x_px - params.margin.left));
        // Use scaleX, handle zero scale case
        if (params.scaleX === 0) return params.zMin_mm;
        return params.zMin_mm + relativeX / params.scaleX;
    }


    // --- Drawing Sub-routines ---

    /** Draws the background, border, axes, ticks, and labels */
    function _drawAxesAndLabels(params) {
        const { margin, plotWidth, plotHeight, zMin_mm, zMax_mm, plotMaxW_um, yCenter } = params;

        // Background/Border
        ctx.fillStyle = DRAW_CONSTANTS.COLOR_BACKGROUND;
        ctx.fillRect(margin.left, margin.top, plotWidth, plotHeight);
        ctx.strokeStyle = DRAW_CONSTANTS.COLOR_PLOT_BORDER;
        ctx.lineWidth = 1;
        ctx.strokeRect(margin.left, margin.top, plotWidth, plotHeight);

        // --- Axes Lines ---
        ctx.strokeStyle = DRAW_CONSTANTS.COLOR_AXIS;
        ctx.lineWidth = 1;

        // X-Axis (Optical Axis)
        if (isFinite(yCenter)) {
             ctx.beginPath();
             ctx.moveTo(margin.left, yCenter);
             ctx.lineTo(margin.left + plotWidth, yCenter);
             ctx.stroke();
        }

        // Y-Axis Line (at z=0 if visible, else at left edge)
        const zeroZ_x = zToX(0, params);
        const drawYAxisAtZero = isFinite(zeroZ_x) && zeroZ_x >= margin.left && zeroZ_x <= margin.left + plotWidth;
        const yAxisLineX = drawYAxisAtZero ? zeroZ_x : margin.left;
        if (isFinite(yAxisLineX)) {
            ctx.beginPath();
            ctx.moveTo(yAxisLineX, margin.top);
            ctx.lineTo(yAxisLineX, margin.top + plotHeight);
            ctx.stroke();
        }

        // --- Ticks and Labels ---
        ctx.fillStyle = DRAW_CONSTANTS.COLOR_TICK_LABEL;
        ctx.font = DRAW_CONSTANTS.FONT_AXIS_LABEL;

        // X-Axis Ticks & Labels
        ctx.textAlign = 'center';
        ctx.textBaseline = 'top';
        if (params.zRange_mm > 1e-9) {
            for (let i = 0; i <= DRAW_CONSTANTS.NUM_X_TICKS; i++) {
                const zTick = zMin_mm + (i / DRAW_CONSTANTS.NUM_X_TICKS) * params.zRange_mm;
                const xTick = zToX(zTick, params);
                if (!isFinite(xTick) || !isFinite(yCenter)) continue;
                ctx.beginPath();
                ctx.moveTo(xTick, yCenter);
                ctx.lineTo(xTick, yCenter + 4);
                ctx.stroke();
                ctx.fillText(zTick.toFixed(0), xTick, yCenter + 6);
            }
        } else { // Single tick if range is zero
             const xTick = margin.left + plotWidth / 2;
             if (isFinite(xTick) && isFinite(yCenter)) {
                 ctx.beginPath();
                 ctx.moveTo(xTick, yCenter);
                 ctx.lineTo(xTick, yCenter + 4);
                 ctx.stroke();
                 ctx.fillText(zMin_mm.toFixed(0), xTick, yCenter + 6);
             }
        }

        // Y-Axis Ticks & Labels
        ctx.textAlign = 'right';
        ctx.textBaseline = 'middle';
        if (plotMaxW_um > 1e-9) {
            for(let i = 0; i <= DRAW_CONSTANTS.NUM_Y_TICKS; i++) {
                const wTick = -plotMaxW_um + (i / DRAW_CONSTANTS.NUM_Y_TICKS) * (2 * plotMaxW_um);
                const yTick = wToY(wTick, params);
                if (!isFinite(yTick) || !isFinite(yAxisLineX)) continue;
                if (yTick >= margin.top - 1 && yTick <= margin.top + plotHeight + 1) {
                     ctx.beginPath();
                     ctx.moveTo(yAxisLineX - 4, yTick);
                     ctx.lineTo(yAxisLineX, yTick);
                     ctx.stroke();
                    // Avoid drawing 0 label if optical axis is already there, unless Y axis is at left edge
                     if (Math.abs(wTick) > 1e-6 || !drawYAxisAtZero || Math.abs(yAxisLineX - margin.left) < 1) {
                         ctx.fillText(wTick.toFixed(0), yAxisLineX - 6, yTick);
                     }
                }
            }
        } else { // Draw 0 tick if plotMaxW is 0
             const yTick = wToY(0, params);
             if (isFinite(yTick) && isFinite(yAxisLineX)) {
                  ctx.beginPath();
                  ctx.moveTo(yAxisLineX - 4, yTick);
                  ctx.lineTo(yAxisLineX, yTick);
                  ctx.stroke();
                  ctx.fillText("0", yAxisLineX - 6, yTick);
             }
        }

        // --- Axis Titles ---
        ctx.fillStyle = DRAW_CONSTANTS.COLOR_AXIS;
        ctx.font = DRAW_CONSTANTS.FONT_AXIS_TITLE;

        // X-Axis Title
        ctx.textAlign = 'center';
        ctx.textBaseline = 'bottom'; // Relative to specified y
        ctx.fillText(`Position z (mm)`, margin.left + plotWidth / 2, params.canvasH - 5); // Position near bottom edge

        // Y-Axis Title (Vertical)
        ctx.save();
        ctx.translate(margin.left / 2.5, margin.top + plotHeight / 2);
        ctx.rotate(-Math.PI / 2);
        ctx.textAlign = 'center';
        ctx.textBaseline = 'bottom'; // Baseline relative to translated origin
        ctx.fillText(`Beam Radius w (µm)`, 0, 0);
        ctx.restore();
    }

    /** Draws the Gaussian beam envelope (fill and stroke) */
    function _drawBeamEnvelope(params) {
        if (!simulationDataCache?.z?.length || simulationDataCache.z.length < 2) return;

        const plotData = simulationDataCache;
        const numPoints = plotData.z.length;

        // --- Define Beam Path ---
        ctx.beginPath();
        const startX = zToX(plotData.z[0], params);
        const startY = wToY(plotData.w[0], params);
        if (!isFinite(startX) || !isFinite(startY)) return; // Cannot draw
        ctx.moveTo(startX, startY);
        for (let i = 1; i < numPoints; i++) {
            const px = zToX(plotData.z[i], params);
            const py = wToY(plotData.w[i], params);
            if (isFinite(px) && isFinite(py)) ctx.lineTo(px, py);
        }
        for (let i = numPoints - 1; i >= 0; i--) {
            const px = zToX(plotData.z[i], params);
            const py = wToY(-plotData.w[i], params);
            if (isFinite(px) && isFinite(py)) ctx.lineTo(px, py);
        }
        ctx.closePath();

        // --- Gaussian Fill ---
        ctx.save();
        ctx.clip(); // Clip subsequent drawing to the beam path

        const xMin = zToX(plotData.z[0], params);
        const xMax = zToX(plotData.z[plotData.z.length - 1], params);
        const stepX = DRAW_CONSTANTS.GAUSSIAN_FILL_SLICE_WIDTH_PX;

        for (let x = xMin; x <= xMax; x += stepX) {
            const z = xToZ(x, params);
            let w = NaN;
            // Linear interpolation for w at z
            for (let i = 0; i < numPoints - 1; i++) {
                if (z >= plotData.z[i] && z <= plotData.z[i+1]) {
                    const dz = plotData.z[i+1] - plotData.z[i];
                    const ratio = (Math.abs(dz) < 1e-9) ? 0 : (z - plotData.z[i]) / dz;
                    w = plotData.w[i] + ratio * (plotData.w[i+1] - plotData.w[i]);
                    break;
                }
            }
            if (isNaN(w)) w = (z <= plotData.z[0]) ? plotData.w[0] : plotData.w[plotData.z.length-1]; // Extrapolation / fallback
            if (!isFinite(w)) continue;

            const topY = wToY(w, params);
            const bottomY = wToY(-w, params);
            if (!isFinite(topY) || !isFinite(bottomY) || bottomY <= topY) continue;

            // Create gradient for this slice
            const gradient = ctx.createLinearGradient(x, topY, x, bottomY);
            const numStops = DRAW_CONSTANTS.GAUSSIAN_FILL_STEPS;
            for (let j = 0; j <= numStops; j++) {
                const t = j / numStops; // 0 to 1
                const normR = 2 * t - 1; // -1 to 1
                const intensity = Math.exp(-(normR * normR)); // Gaussian falloff
                gradient.addColorStop(t, `rgba(100, 100, 255, ${0.5 * intensity})`);
            }
            ctx.fillStyle = gradient;
            ctx.fillRect(x, topY, stepX, bottomY - topY);
        }
        ctx.restore(); // Remove clipping path

        // --- Stroke Beam Outline ---
        // Re-uses the path defined earlier
        ctx.strokeStyle = DRAW_CONSTANTS.COLOR_BEAM_STROKE;
        ctx.lineWidth = 1.5;
        ctx.stroke();
    }

    /** Draws wavefronts within the beam envelope */
    function _drawWavefronts(params) {
        if (!simulationDataCache?.z?.length || simulationDataCache.z.length < 2) return;

        const plotData = simulationDataCache;
        const { margin, plotHeight, plotWidth, zMin_mm, zMax_mm, scaleX, yCenter } = params;
        const numPoints = plotData.z.length;
        let wavefrontsDrawn = 0;
        let lastWavefrontZ = -Infinity;

        ctx.save(); // Save before clipping/style change
        ctx.strokeStyle = DRAW_CONSTANTS.COLOR_WAVEFRONT;
        ctx.lineWidth = 1.0;

        // --- Define Clipping Path (Beam Envelope) ---
        ctx.beginPath();
        const startX = zToX(plotData.z[0], params);
        const startY = wToY(plotData.w[0], params);
        if (!isFinite(startX) || !isFinite(startY)) { ctx.restore(); return; } // Cannot clip
        ctx.moveTo(startX, startY);
        for (let i = 1; i < numPoints; i++) {
            const px = zToX(plotData.z[i], params);
            const py = wToY(plotData.w[i], params);
            if (isFinite(px) && isFinite(py)) ctx.lineTo(px, py);
        }
        for (let i = numPoints - 1; i >= 0; i--) {
            const px = zToX(plotData.z[i], params);
            const py = wToY(-plotData.w[i], params);
            if (isFinite(px) && isFinite(py)) ctx.lineTo(px, py);
        }
        ctx.closePath();
        ctx.clip(); // Apply clipping

        // --- Draw Wavefronts ---
        for (let i = 0; i < numPoints && wavefrontsDrawn < DRAW_CONSTANTS.MAX_WAVEFRONTS; i++) {
            const z_mm = plotData.z[i];
            const w_um = plotData.w[i];
            const R_mm = plotData.R[i];

            if (z_mm >= lastWavefrontZ + DRAW_CONSTANTS.WAVEFRONT_SPACING_MM) {
                const current_x = zToX(z_mm, params);
                if (!isFinite(current_x) || !isFinite(w_um)) continue;

                const y_top = wToY(w_um, params);
                const y_bottom = wToY(-w_um, params);
                 if (!isFinite(y_top) || !isFinite(y_bottom)) continue;

                ctx.beginPath();
                if (!isFinite(R_mm)) { // Flat Wavefront (R=Infinity)
                    ctx.moveTo(current_x, y_top);
                    ctx.lineTo(current_x, y_bottom);
                } else if (Math.abs(R_mm) > 1e-6 && scaleX > 0) { // Curved Wavefront
                    const R_px = R_mm * scaleX; // Radius in canvas X units
                    const centerX_px = current_x - R_px;
                    const radius_px = Math.abs(R_px);
                    const w_px = Math.abs(y_top - yCenter); // Use calculated y_top

                    if (isFinite(centerX_px) && isFinite(w_px) && radius_px > w_px && w_px > 0) {
                        const asin_arg = Math.max(-1, Math.min(1, w_px / radius_px));
                        const angle_extent = Math.asin(asin_arg);
                        let startAngle, endAngle;
                        if (R_mm > 0) { // Diverging (center left)
                            startAngle = -angle_extent; endAngle = angle_extent;
                        } else { // Converging (center right)
                            startAngle = Math.PI - angle_extent; endAngle = Math.PI + angle_extent;
                        }
                        if (isFinite(startAngle) && isFinite(endAngle)) {
                            ctx.arc(centerX_px, yCenter, radius_px, startAngle, endAngle);
                        }
                    }
                }
                 // Stroke only if path was generated (flat or valid arc)
                 if (!ctx.isEmpty) { // Check if path has segments (modern browsers)
                      // Fallback check: Count points in path (less efficient)
                      // if (ctx.getPathData && ctx.getPathData().length > 0) {
                     ctx.stroke();
                     wavefrontsDrawn++;
                     lastWavefrontZ = z_mm;
                     // }
                 }
            }
        }
        ctx.restore(); // Restore context state (remove clipping)
    }

    /** Draws the optical element symbols and labels */
    function _drawOpticalElements(params) {
        if (!opticalElementsRef) return;

        const { margin, plotWidth, plotHeight, yCenter } = params;
        const symbolDrawHeight = plotHeight * DRAW_CONSTANTS.ELEMENT_SYMBOL_HEIGHT_FACTOR;
        const y1_draw = yCenter - symbolDrawHeight / 2; // Top Y for drawing symbol
        const y2_draw = yCenter + symbolDrawHeight / 2; // Bottom Y

        ctx.font = DRAW_CONSTANTS.FONT_ELEMENT_LABEL;
        ctx.textAlign = 'center';
        ctx.textBaseline = 'bottom';

        const formatElementType = (type) => type ? type.replace(/_/g, ' ').replace(/\b\w/g, l => l.toUpperCase()) : "Element";

        opticalElementsRef.forEach((element, index) => {
            const x = zToX(element.position_mm, params);

            // Check if element is within visible plot area
            if (isFinite(x) && x >= margin.left - 1 && x <= margin.left + plotWidth + 1) {
                const elementType = element.type;
                const f_mm = element.property?.f_mm; // Check lens focal length
                let isLens = elementType === 'lens' && typeof f_mm === 'number' && isFinite(f_mm);
                const halfSymbolWidth = DRAW_CONSTANTS.LENS_SYMBOL_WIDTH_PX / 2;

                ctx.beginPath(); // Start path for the element symbol

                if (isLens && f_mm > 0) { // Converging Lens ()
                    const xL = x - halfSymbolWidth/2, xR = x + halfSymbolWidth/2;
                    const ctrlX_L = x - DRAW_CONSTANTS.LENS_SYMBOL_WIDTH_PX; // Wider control point
                    const ctrlX_R = x + DRAW_CONSTANTS.LENS_SYMBOL_WIDTH_PX;
                    ctx.moveTo(xL, y1_draw);
                    ctx.lineTo(xR, y1_draw);
                    ctx.quadraticCurveTo(ctrlX_R, yCenter, xR, y2_draw);
                    ctx.lineTo(xL, y2_draw);
                    ctx.quadraticCurveTo(ctrlX_L, yCenter, xL, y1_draw);
                } else if (isLens && f_mm < 0) { // Diverging Lens )(
                    const xL = x - halfSymbolWidth, xR = x + halfSymbolWidth;
                    const ctrlX = x; // Center control point
                    ctx.moveTo(xL, y1_draw);
                    ctx.lineTo(xR, y1_draw);
                    ctx.quadraticCurveTo(ctrlX, yCenter, xR, y2_draw);
                    ctx.lineTo(xL, y2_draw);
                    ctx.quadraticCurveTo(ctrlX, yCenter, xL, y1_draw);
                } else { // Default Rectangle (or f_mm == 0 lens)
                    ctx.rect(x - halfSymbolWidth, y1_draw, DRAW_CONSTANTS.LENS_SYMBOL_WIDTH_PX, symbolDrawHeight);
                }
                // No need for closePath() if last point connects to start

                // Fill and Stroke the symbol
                ctx.fillStyle = DRAW_CONSTANTS.COLOR_ELEMENT_FILL;
                ctx.fill();
                ctx.strokeStyle = DRAW_CONSTANTS.COLOR_ELEMENT_STROKE;
                ctx.lineWidth = 1.5;
                ctx.stroke();

                // Draw Label above the symbol
                ctx.fillStyle = DRAW_CONSTANTS.COLOR_ELEMENT_LABEL;
                const label = `${formatElementType(elementType)} ${index + 1}`;
                const labelY = Math.min(y1_draw - 3, margin.top + plotHeight); // Ensure within top margin space
                ctx.fillText(label, x, labelY);

                // Update hit rectangle (wider for easier grabbing)
                 element.canvasRect = {
                    x: x - DRAW_CONSTANTS.ELEMENT_HIT_TOLERANCE_PX,
                    y: y1_draw,
                    w: DRAW_CONSTANTS.ELEMENT_HIT_TOLERANCE_PX * 2,
                    h: symbolDrawHeight
                 };

            } else {
                element.canvasRect = null; // Not visible or invalid position
            }
        });
         // Reset styles
         ctx.lineWidth = 1;
         ctx.fillStyle = '#000000';
         ctx.strokeStyle = '#000000';
    }


    /** Main internal drawing function, orchestrates the drawing process */
    function _drawInternal() {
        if (!ctx || !canvas) return;

        const params = getDrawParams();

        // Clear canvas
        ctx.clearRect(0, 0, canvas.width, canvas.height);

        if (!params || !opticalElementsRef || !simulationDataCache) {
            // Draw placeholder text if data/params are not ready
            ctx.fillStyle = DRAW_CONSTANTS.COLOR_WAITING_TEXT;
            ctx.textAlign = "center";
            ctx.textBaseline = "middle";
            ctx.font = DRAW_CONSTANTS.FONT_AXIS_LABEL;
            ctx.fillText("Waiting for simulation data...", canvas.width / 2, canvas.height / 2);
            return;
        }

        // --- Perform Drawing in Order ---
        _drawAxesAndLabels(params);   // Background, Axes, Ticks, Labels
        _drawBeamEnvelope(params);    // Beam fill and stroke
        _drawWavefronts(params);      // Wavefronts (clipped inside beam)
        _drawOpticalElements(params); // Elements and their labels (on top)
    }

    // --- Event Handlers ---
    function handleDragStart(e) {
        if (!opticalElementsRef || !canvas) return;
        const pos = getEventPos(e);
        if (e.type === 'touchstart') e.preventDefault(); // Prevent scroll on touch

        draggedElement = findElementAtPos(pos);
        if (draggedElement) {
            isDragging = true;
            canvas.classList.add('dragging');
            canvas.classList.remove('draggable'); // Hide hover effect while dragging
        }
    }

    function handleDragMove(e) {
        if (!canvas) return;
        const pos = getEventPos(e);

        if (isDragging && draggedElement) {
            if (e.type === 'touchmove') e.preventDefault(); // Prevent scroll during touch drag

            const params = getDrawParams();
            if (!params) return; // Need params for coordinate conversion

            const newZ = xToZ(pos.x, params);
            if (!isFinite(newZ)) return; // Ignore invalid positions

            // Find index (necessary if elements array is modified elsewhere)
            const elementIndex = opticalElementsRef.findIndex(el => el.id === draggedElement.id);
            if (elementIndex > -1) {
                 // Check for significant change before updating
                 const currentZ = opticalElementsRef[elementIndex].position_mm;
                 const minZChange = (params.scaleX > 0)
                    ? (DRAW_CONSTANTS.DRAG_UPDATE_MIN_PIXEL_CHANGE / params.scaleX)
                    : 0.1; // Min change in mm

                 if (Math.abs(currentZ - newZ) > minZChange) {
                     opticalElementsRef[elementIndex].position_mm = newZ;
                     if (simulationUpdateCallback) {
                         simulationUpdateCallback(); // Request simulation update
                     }
                     // Redraw will happen when new simulation data arrives via public draw()
                 }
            }
        } else if (e.type.startsWith('mouse')) { // Handle hover effect if not dragging (mouse only)
            const elementUnderMouse = findElementAtPos(pos);
            if (elementUnderMouse) {
                canvas.classList.add('draggable');
            } else {
                canvas.classList.remove('draggable');
            }
        }
    }

    function handleDragEnd(e) {
        const wasDragging = isDragging; // Capture state before reset
        isDragging = false;
        draggedElement = null;

        if (canvas) {
            canvas.classList.remove('dragging');

            // Check hover state again after drag ends (or on mouseleave)
            const pos = getEventPos(e); // Get current position
            // Only show hover if the mouse is still over an element AND not leaving canvas
             const elementUnderMouse = (e.type !== 'mouseleave') ? findElementAtPos(pos) : null;

            if (elementUnderMouse) {
                 canvas.classList.add('draggable');
            } else {
                 canvas.classList.remove('draggable');
            }
        }

        // Trigger a final update if a drag just finished to ensure latest position is simulated
        if (wasDragging && simulationUpdateCallback) {
             simulationUpdateCallback();
        }
    }

     /** Attaches or re-attaches event listeners */
     function setupEventListeners() {
         if (!canvas) return;

         // Remove potentially existing listeners first to prevent duplicates
         canvas.removeEventListener('mousedown', handleDragStart);
         window.removeEventListener('mousemove', handleDragMove);
         window.removeEventListener('mouseup', handleDragEnd);
         canvas.removeEventListener('mouseleave', handleDragEnd);
         canvas.removeEventListener('touchstart', handleDragStart);
         canvas.removeEventListener('touchmove', handleDragMove);
         canvas.removeEventListener('touchend', handleDragEnd);
         canvas.removeEventListener('touchcancel', handleDragEnd);

         // Add Mouse Listeners (window for move/up to catch events outside canvas)
         canvas.addEventListener('mousedown', handleDragStart);
         window.addEventListener('mousemove', handleDragMove);
         window.addEventListener('mouseup', handleDragEnd);
         canvas.addEventListener('mouseleave', handleDragEnd);

         // Add Touch Listeners ({ passive: false } to allow preventDefault)
         canvas.addEventListener('touchstart', handleDragStart, { passive: false });
         canvas.addEventListener('touchmove', handleDragMove, { passive: false });
         canvas.addEventListener('touchend', handleDragEnd);
         canvas.addEventListener('touchcancel', handleDragEnd);
     }


    // --- Public Interface ---
    return {
        /**
         * Initializes the CanvasController.
         * @param {HTMLCanvasElement} canvasElement - The canvas DOM element.
         * @param {OpticalElement[]} elementsArray - Reference to the main opticalElements array.
         * @param {BeamParams} beamParams - Reference to the main beamParams object.
         * @param {Function} updateCallback - Function to call to trigger a simulation update.
         */
        init: (canvasElement, elementsArray, beamParams, updateCallback) => {
            canvas = canvasElement;
            if (!canvas) {
                console.error("CanvasController init: Canvas element not provided.");
                return;
            }
            ctx = canvas.getContext('2d');
            if (!ctx) {
                 console.error("CanvasController init: Failed to get 2D context.");
                 canvas = null; return;
            }

            opticalElementsRef = elementsArray;
            beamParamsRef = beamParams;
            simulationUpdateCallback = updateCallback;
            simulationDataCache = null; // Reset cache on init
            isDragging = false; // Reset drag state
            draggedElement = null;

            setupEventListeners();

            // Initial resize and draw placeholder
            CanvasController.handleResize(); // Call public resize
            requestAnimationFrame(_drawInternal); // Draw placeholder or initial data if available (unlikely on init)

            console.log("CanvasController initialized.");
        },

        /** Resizes the canvas based on parent container and aspect ratio. */
        handleResize: () => {
             if (!canvas || !ctx) return;

             const container = canvas.parentElement;
             if (!container) return;

             const cs = window.getComputedStyle(container);
             const containerPaddingX = parseFloat(cs.paddingLeft) + parseFloat(cs.paddingRight);
             const containerBorderX = parseFloat(cs.borderLeftWidth) + parseFloat(cs.borderRightWidth);
             const availableWidth = container.clientWidth - containerPaddingX - containerBorderX;

             const targetWidth = Math.max(DRAW_CONSTANTS.MIN_CANVAS_WIDTH, Math.min(availableWidth, DRAW_CONSTANTS.MAX_CANVAS_WIDTH));
             const targetHeight = Math.max(DRAW_CONSTANTS.MIN_CANVAS_HEIGHT, Math.round(targetWidth / DRAW_CONSTANTS.TARGET_ASPECT_RATIO));

             if (canvas.width !== targetWidth || canvas.height !== targetHeight) {
                  console.log(`CanvasController resizing canvas to ${targetWidth}x${targetHeight}`);
                  canvas.width = targetWidth;
                  canvas.height = targetHeight;
                  // Redraw needed after resize
                  requestAnimationFrame(_drawInternal);
             }
         },

        /**
         * Updates the cached simulation data and triggers a redraw.
         * @param {SimulationResult | null} plotData - The simulation data { z: [], w: [], R: [] } or null.
         */
        draw: (plotData) => {
             simulationDataCache = plotData; // Cache the latest data (even if null)
             if (canvas && ctx) { // Ensure canvas/context are valid
                 requestAnimationFrame(_drawInternal); // Request redraw on next frame
             }
        }
    };
})();

// --- END OF FILE interactiveCanvas.js ---