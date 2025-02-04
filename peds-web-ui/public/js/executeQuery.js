document.addEventListener('DOMContentLoaded', () => {
    const executeQueryButton = document.getElementById('generateQueryButton');
    const queryInput = document.getElementById('queryInput');
    const kInput = document.getElementById('kInput').value.trim(); 
    // const displayInputQuery = document.getElementById('displayIGQuery')
    
    executeQueryButton.addEventListener('click', async (event) => {
        event.preventDefault(); // Prevent default form submission
        console.log("executeQueryButton clicked!");

        const igDiv = document.getElementById('igDiv');
        igDiv.style.display = "none";

        const executeQueryDiv = document.getElementById('executeQueryDiv');
        executeQueryDiv.style.display = 'block';

        const displayInputQuery = document.getElementById('displayInputQuery');
        displayInputQuery.style.display = 'block';

        const executeQuerySection = document.getElementById('executeQuerySection');
        executeQuerySection.style.display = 'block';

        window.query = queryInput.value.trim(); // Get the query from input
        window.igQuery = `IG OF(${query});`; //creating igQuery here

        window.estInput = document.getElementById('estimateInput');
        window.estInput.placeholder = igQuery;

        window.explQuery = `IGEXPL TOP ${kInput} OF(${query});`; //creating explQuery here
        window.explInput = document.getElementById('explInput');
        window.explInput.placeholder = explQuery;

        if (!query) {
            displayInputQuery.innerHTML = '<p style="color: red;">Please enter a SQL query!</p>';
            return;
        }

        try {
            const response = await fetch('/execute-query', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ query }),
            });

            const result = await response.json();

            if (response.ok) {
                displayInputQuery.innerHTML = `
                    <h3>Script Output:</h3>
                `;
                const rawData = result.output;
                const { headers, data } = processInputData(rawData);

                // Create a table
                createInputTable(headers, data);
            }
            else {
                displayInputQuery.innerHTML = `
                    <h3>Error:</h3>
                    <p style="color: red;">${result.error}</p>
                `;
            }
        } catch (error) {
            console.error('Error executing query:', error);
            displayInputQuery.innerHTML = '<p style="color: red;">An error occurred while executing the query.</p>';
        }
    });
});

function processInputData(rawData) {
    const lines = rawData.trim().split('\n').map(line => line.replace(/\|+$/, ''));
    
    // Extract headers from the first line
    const headers = lines[0].split('|').map(header => header.trim());
    
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

function createInputTable(headers, data) {
    const tableContainer = document.getElementById('displayInputTable');
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