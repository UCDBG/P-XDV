document.addEventListener('DOMContentLoaded', () => {
    const generateExpl = document.getElementById('generateExpl');
    const queryInput = document.getElementById('queryInput'); // Step 2 input field
    const explDiv = document.getElementById('explDiv');
    const displayexplQuery = document.getElementById('displayexplQuery');

    generateExpl.addEventListener('click', async () => {
        console.log("clicked EXPL button");
        const kInput = document.getElementById('kInput').value.trim(); //top k elements
        explDiv.style.display = "block";
        // Grab the query from Step 2
        const query = queryInput.value.trim();
        window.explQuery = `IGEXPL TOP ${kInput} OF(${query});`; //creating explQuery here
        window.explInput = document.getElementById('explInput');
        window.explInput.placeholder = explQuery;
        if (!query) {
            displayexplQuery.innerHTML = '<p style="color: red;">No query provided from Step 2.</p>';
            return;
        }

        try {
            console.log("inside try block");
            // Send the query to the backend
            const response = await fetch('/expl-peds', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ query,kInput }),
            });

            const result = await response.json();

            // Display the result
            if (response.ok) {
                displayexplQuery.innerHTML = `
                    <h3>EXPL Script Output:</h3>
                `;
                const rawData = result.output;
                const { headers, data } = processExplData(rawData);
                createExplTable(headers, data);

            } else {
                displayexplQuery.innerHTML = `
                    <h3>Error:</h3>
                    <p style="color: red;">${result.error}</p>
                `;
            }
        } catch (error) {
            console.error('Error estimating price:', error);
            displayexplQuery.innerHTML = '<p style="color: red;">An unexpected error occurred.</p>';
        }
    });
});

function processExplData(rawData) {
    const lines = rawData.trim().split('\n').map(line => line.replace(/\|+$/, ''));
    
    // Extract headers from the first line
    // const headers = lines[0].split('|').map(header => header.trim());
    const headers = lines[0].split('|').map(header => header.trim().replace(/IG/g, 'DG'));

    // Extract rows from the remaining lines (starting from the third line)
    const rows = lines.slice(2).map(row =>
        row.split('|').map(cell => cell.trim())
    );

    // Map rows into objects with headers as keys
    const data = rows.map(row =>
        headers.reduce((obj, header, index) => {
            obj[header] = row[index]; // Map each cell to its corresponding header
            return obj;
        }, {})
    );

    return { headers, data };
}

function createExplTable(headers, data) {
    const tableContainer = document.getElementById('displayexplQuery');
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
