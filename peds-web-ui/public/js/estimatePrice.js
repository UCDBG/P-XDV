document.addEventListener('DOMContentLoaded', () => {
    const generateIGButton = document.getElementById('generateIGbutton');
    const estimateInput = document.getElementById('estimateInput');
    const queryInput = document.getElementById('queryInput'); // Step 2 input field
    const igDiv = document.getElementById('igDiv');
    const displayIGQuery = document.getElementById('displayIGQuery');

    generateIGButton.addEventListener('click', async () => {
        //resetting step 2
        const executeQueryDiv = document.getElementById('executeQueryDiv');
        executeQueryDiv.style.paddingTop = '20px';
        executeQueryDiv.style.display = 'none';

        const displayInputQuery = document.getElementById('displayInputQuery');
        displayInputQuery.style.display = 'none';

        const executeQuerySection = document.getElementById('executeQuerySection');
        executeQuerySection.style.display = 'none';

        igDiv.style.display = "block";
        // Grab the query from Step 2
        const query = queryInput.value.trim();
        console.log("query from estimate price function", query);
        if (!query) {
            displayIGQuery.innerHTML = '<p style="color: red;">No query provided.</p>';
            return;
        }

        try {
            // Send the query to the backend
            const response = await fetch('/estimate-price', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ query }),
            });

            const result = await response.json();

            if (response.ok) {
                displayIGQuery.innerHTML = `
                    <h3>Script Output:</h3>
                `;
                const rawData = result.output;
                const { headers, data } = processData(rawData);

                // Create a table
                createTable(headers, data);
                
                // Attributes to filter
                const attributes = Object.keys(data[0]).filter(attr => attr.startsWith("DG_"));
                // Modify DG_owned_lowrisk to DG_risklevel in a separate step
                for (let i = 0; i < attributes.length; i++) {
                    if (attributes[i] === "DG_owned_lowrisk") {
                        attributes[i] = "DG_risklevel";
                    }
                }
                // Setup checkboxes and generate the initial graph
                setupAttributeCheckboxes(attributes, data);
                createBarGraph(attributes, data, 1);
                setupRangeFiltering(attributes, data);
            }
            else {
                displayIGQuery.innerHTML = `
                    <h3>Error:</h3>
                    <p style="color: red;">${result.error}</p>
                `;
            }
        } catch (error) {
            console.error('Error estimating price:', error);
            displayIGQuery.innerHTML = '<p style="color: red;">An unexpected error occurred.</p>';
        }
    });
});

// Utility function to rename headers dynamically
function renameHeader(header) {
    let newHeader = header;

    // Apply renaming rules
    if (newHeader.includes('left')) {
        newHeader = newHeader.replace('left', 'owned');
    }
    if (newHeader.includes('right')) {
        newHeader = newHeader.replace('right', 'shared');
    }
    if (newHeader.includes('IG')) {
        newHeader = newHeader.replace('IG', 'DG');
    }
    newHeader = newHeader.replace('integ', ''); // Remove "integ"

    // Clean up extra underscores or trailing spaces
    return newHeader.replace(/_+/g, '_').replace(/_$/, '').trim();
}

function processData(rawData) {
    const lines = rawData.trim().split('\n').map(line => line.replace(/\|+$/, ''));
    const headers = lines[0].split('|').map(header => header.trim());

    const rows = lines.slice(2).map(row =>
        row.split('|').map(cell => cell.trim())
    );

    // Filter out "hamming" columns
    const filteredHeaders = headers.filter(
        header => !header.startsWith('hamming') && !header.includes('conv')
    );

    const filteredIndexes = headers
        .map((header, index) =>
            !header.startsWith('hamming') && !header.includes('conv') ? index : -1
        )
        .filter(index => index !== -1);

    // Apply the renaming rules to filteredHeaders
    const renamedHeaders = filteredHeaders.map(renameHeader);

    // Modify DG_owned_lowrisk to DG_risklevel in a separate step
    for (let i = 0; i < filteredHeaders.length; i++) {
        if (filteredHeaders[i] === "IG_left_lowrisk_integ") {
            filteredHeaders[i] = "DG_risklevel";
        }
    }
    // Modify DG_owned_lowrisk to DG_risklevel in a separate step
    for (let i = 0; i < renamedHeaders.length; i++) {
        if (renamedHeaders[i] === "DG_owned_lowrisk") {
            renamedHeaders[i] = "DG_risklevel";
        }
    }

    // Process the data
    const data = rows.map(row =>
        filteredIndexes.reduce((obj, index, i) => {
            const originalKey = filteredHeaders[i];
            const newKey = renameHeader(originalKey); // Rename dynamically
            obj[newKey] = row[index];
            return obj;
        }, {})
    );

    return { headers: renamedHeaders, data };
}

function createTable(headers, data) {
    const tableContainer = document.getElementById('tableContainer');
    // Check if a table already exists within the container
    const existingTable = tableContainer.querySelector('table');

    if (existingTable) {
    // Remove the existing table
    existingTable.remove();
    }
    const table = document.createElement('table');

    // Add headers
    const thead = table.createTHead();
    const headerRow = thead.insertRow();
    headers.forEach(header => {
        const th = document.createElement('th');
        th.textContent = header;
        headerRow.appendChild(th);
    });

    // Add rows
    const tbody = table.createTBody();
    data.forEach(row => {
        const rowElement = tbody.insertRow();
        headers.forEach(header => {
            const cell = rowElement.insertCell();
            cell.textContent = row[header];
        });
    });

    //creating the able in a div
    tableContainer.appendChild(table);
    
}

let currentFilteredData = null; // Stores the currently filtered dataset
let currentStartRange = 1; // Tracks the starting range for x-axis labels

let myChart = null;
function createBarGraph(filteredAttributes, fullDataset, startRange) {
    const ctx = document.getElementById("myChart1").getContext("2d");

    // Filter dataset for selected attributes
    const filteredData = fullDataset.map(row => {
        const filteredRow = {};
        filteredAttributes.forEach(attr => {
            filteredRow[attr] = row[attr];
        });
        // Always include Total_DG in filteredRow
        // filteredRow["Total_DG"] = row["Total_DG"];
        
        return filteredRow;
    });

    // const labels = filteredData.map((_, index) => `DataPoint ${index + 1}`);
    const labels = filteredData.map((_, index) => `DataPoint ${index + startRange}`);

    // Generate datasets with dynamic colors
    const datasets = filteredAttributes.map(attribute => {
        const backgroundColor = generateColor(attribute, 0.8, 10); // Slightly transparent and lighter
        const borderColor = generateColor(attribute, 1, 0); // Solid border color

        return {
            label: attribute,
            data: filteredData.map(row => row[attribute]),
            backgroundColor,
            borderColor,
            borderWidth: 1,
        };
    });

    // Tooltips use full dataset
    const tooltipCallback = (tooltipItem) => {
        const index = tooltipItem.dataIndex;
        const tooltipData = fullDataset[index];
        return Object.entries(tooltipData)
            .map(([key, value]) => `${key}: ${value}`);
    };

    const options = {
        responsive: true,
        plugins: {
            tooltip: {
                callbacks: {
                    label: tooltipCallback,
                },
            },
        },
        scales: {
            x: {
                stacked: true,
                title: {
                    display: true, // Show the title
                    text: 'Data Points', // Set x-axis label
                },
            },
            y: {
                stacked: true,
                title: {
                    display: true, // Show the title
                    text: 'Total DG', // Set y-axis label
                },
            },
        },
    };

    // Destroy existing chart instance, if any
    if (myChart) {
        myChart.destroy();
    }

    // Create and assign a new chart instance
    myChart = new Chart(ctx, {
        type: "bar",
        data: {
            labels: labels,
            datasets: datasets,
        },
        options: options,
    });
}

const colorCache = {}; // Cache for consistent colors

// Function to generate a unique HSL color for an attribute
function generateColor(attribute, transparency = 1, brightnessAdjustment = 0) {
    // Check if the color is already cached
    if (colorCache[attribute]) {
        return adjustColor(colorCache[attribute], transparency, brightnessAdjustment);
    }

    // Generate a unique hue based on the attribute name
    const hash = [...attribute].reduce((acc, char) => acc + char.charCodeAt(0), 0);
    const hue = hash % 360; // Map hash to a 0-360 range
    const baseColor = `hsl(${hue}, 70%, 50%)`;

    // Cache the generated color
    colorCache[attribute] = baseColor;

    return adjustColor(baseColor, transparency, brightnessAdjustment);
}

// Function to adjust color brightness or add transparency
function adjustColor(color, transparency = 1, brightnessAdjustment = 0) {
    const hslMatch = color.match(/hsl\((\d+),\s*(\d+)%,\s*(\d+)%\)/);
    if (!hslMatch) return color; // Return original color if not HSL

    let [h, s, l] = hslMatch.slice(1).map(Number);
    l = Math.min(100, Math.max(0, l + brightnessAdjustment)); // Adjust brightness
    return `hsla(${h}, ${s}%, ${l}%, ${transparency})`;
}

function setupAttributeCheckboxes(attributes, fullDataset) {
    const container = document.getElementById("attributeCheckboxes");
    container.innerHTML = ""; // Clear existing checkboxes

    attributes.forEach(attribute => {
        const checkbox = document.createElement("input");
        checkbox.type = "checkbox";
        checkbox.id = `checkbox_${attribute}`;
        checkbox.checked = true; // Default to checked
        checkbox.dataset.attribute = attribute;

        // Add event listener to dynamically update the chart
        checkbox.addEventListener("change", () => {
            const selectedAttributes = Array.from(
                container.querySelectorAll("input:checked")
            ).map(input => input.dataset.attribute);

            // Use the current filtered dataset and start range
            createBarGraph(selectedAttributes, currentFilteredData || fullDataset, currentStartRange);
        
        });

        const label = document.createElement("label");
        label.htmlFor = checkbox.id;
        label.innerText = attribute;

        container.appendChild(checkbox);
        container.appendChild(label);
    });
}

function setupRangeFiltering(filteredAttributes, fullDataset) {
    document.getElementById('applyRangeButton').addEventListener('click', (event) => {
        event.preventDefault();

        // Get the range values from input fields
        const startRange = parseInt(document.getElementById('startRange').value, 10);
        const endRange = parseInt(document.getElementById('endRange').value, 10);
        let dataLen = null;
        dataLen = fullDataset.length;

        // Validate the range input
        if (
            isNaN(startRange) ||
            isNaN(endRange) ||
            startRange < 1 ||
            endRange > dataLen ||
            startRange > endRange
        ) {
            alert(`Invalid range! Please enter a valid range (e.g., DataPoint 1 to DataPoint ${dataLen}).`);
            return;
        }

        // Filter fullDataset for the selected range
        currentFilteredData = fullDataset.slice(startRange - 1, endRange);
        currentStartRange = startRange; // Update the global start range

        // Update the bar graph with the filtered data
        createBarGraph(filteredAttributes, currentFilteredData, currentStartRange);
    });
}