document.addEventListener('DOMContentLoaded', () => {
    console.log('Page is fully loaded and parsed');
    const importButtonOwned = document.getElementById('importDataButtonOwned');
    const importButtonShared = document.getElementById('importDataButtonShared');
    const csvFileInputOwned = document.getElementById('csvFileInputOwned');
    const csvFileInputShared = document.getElementById('csvFileInputShared');
    const tableNameInputOwned = document.getElementById('tableNameInputOwned');
    const tableNameInputShared = document.getElementById('tableNameInputShared');

    //displaying schema here
    fetchAndDisplaySchema();

    // Refresh schema on button click
    document.getElementById('refreshSchemaButton').addEventListener('click', async () => {
        await fetchAndDisplaySchema(); // Refresh only the schema container
    });

    // Import button clicked
    importButtonOwned.addEventListener('click', () => {
        csvFileInputOwned.click();
    });

    importButtonShared.addEventListener('click', () => {
        csvFileInputShared.click();
    });

    // upload to owned schema
    csvFileInputOwned.addEventListener('change', async (event) => {
        const file = event.target.files[0];
        if (file) {
            const reader = new FileReader();

            reader.onload = async (e) => {
                const csvData = e.target.result;

                // Get the table name (if provided)
                let tableName = tableNameInputOwned.value.trim();
                if (!tableName) {
                    tableName = file.name.split('.')[0]; // Default to file name without extension
                }

                try {
                    const response = await fetch('/uploadOwned', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ csvData, tableName }),
                    });

                    if (response.ok) {
                        alert('CSV data uploaded successfully!');
                        tableNameInputOwned.style.display = 'block';
                    } else if (response.status === 409) {
                        const data = await response.json();
                        alert(data.message);
                        tableNameInputOwned.style.display = 'block';
                    } else {
                        alert('Failed to upload CSV.');
                    }
                } catch (error) {
                    console.error('Error uploading file:', error);
                    alert('An error occurred while uploading the file.');
                }
            };

            reader.readAsText(file);
        }
    });

    // upload to shared schema
    csvFileInputShared.addEventListener('change', async (event) => {
        const file = event.target.files[0];
        if (file) {
            const reader = new FileReader();

            reader.onload = async (e) => {
                const csvData = e.target.result;

                // Get the table name (if provided)
                let tableName = tableNameInputShared.value.trim();
                if (!tableName) {
                    tableName = file.name.split('.')[0]; // Default to file name without extension
                }

                try {
                    const response = await fetch('/uploadShared', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ csvData, tableName }),
                    });

                    if (response.ok) {
                        alert('CSV data uploaded successfully!');
                        tableNameInputShared.style.display = 'block';
                    } else if (response.status === 409) {
                        const data = await response.json();
                        alert(data.message);
                        tableNameInputShared.style.display = 'block';
                    } else {
                        alert('Failed to upload CSV.');
                    }
                } catch (error) {
                    console.error('Error uploading file:', error);
                    alert('An error occurred while uploading the file.');
                }
            };
            reader.readAsText(file);
        }
    });
});


// Function to fetch and display the schema
async function fetchAndDisplaySchema() {
    const schemaContainerL = document.getElementById('schemaContainerL');
    const schemaContainerR = document.getElementById('schemaContainerR');
    try {
        const responseOwned = await fetch('/schemaOwned');
        const responseShared = await fetch('/schemaShared');
        if (!responseOwned.ok) {
            throw new Error('Failed to fetch owned schema');
        }
        if (!responseShared.ok) {
            throw new Error('Failed to fetch shared schema');
        }

        const tablesOwned = await responseOwned.json();
        const tablesShared = await responseShared.json();

        // Clear previous schema
        schemaContainerL.innerHTML = '';
        schemaContainerR.innerHTML = '';
        createSchema(tablesOwned, schemaContainerL);
        createSchema(tablesShared, schemaContainerR);
    } catch (error) {
        console.error('Error fetching schema:', error);
        schemaContainerL.innerHTML = '<p>Error fetching schema. Please try again.</p>';
        schemaContainerR.innerHTML = '<p>Error fetching schema. Please try again.</p>';
    }
}

function createSchema(tables, schemaContainer) {
        // Create a single table for displaying all schemas
        const schemaTable = document.createElement('table');
        schemaTable.style.width = '95%';
        schemaTable.style.borderCollapse = 'collapse';
        schemaTable.style.marginTop = '10px';

        // Add headers
        const headerRow = document.createElement('tr');
        headerRow.innerHTML = `
            <th style="border: 1px solid #ccc; padding: 8px; text-align: left;">Table Name</th>
            <th style="border: 1px solid #ccc; padding: 8px; text-align: left;">Attributes</th>
        `;

        schemaTable.appendChild(headerRow);

        // Add rows for each table
        tables.forEach(table => {
            const row = document.createElement('tr');

            // Format attributes as "name(type)"
            const attributes = table.schema
                .map(col => `${col.column_name}(${col.data_type})`)
                .join(', ');

            row.innerHTML = `
                <td style="border: 1px solid #ccc; padding: 8px;">${table.table_name}</td>
                <td style="border: 1px solid #ccc; padding: 8px;">${attributes}</td>
            `;
            schemaTable.appendChild(row);
        });

        schemaContainer.appendChild(schemaTable);
}