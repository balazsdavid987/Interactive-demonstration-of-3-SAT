// Global variables
var current = {};
var letters = 'abcdefgh';
var colors = {
  white: '#FFFFFF',
  grey:  '#D7D7D7',
  black: '#1D1D1D'
};

// Initilization

(function() {
  // default values
  // (although the layout supports only n = 5, the functions
  // were written to work with any n)
  current.n = 5;

  current.showImpliedClauses =  true;

  // add event listener to #toggleImpliedClauses and set "checked" status
  var element = document.getElementById('toggleImpliedClauses');
  element.addEventListener('click', toggleImpliedClauses);
  if(current.showImpliedClauses) {
    element.checked = true;
  }
  
  // create truthtable related variables
  current.truthtable = [];
  current.satisfyingassignments = Math.pow(2, current.n);
  for(var a = 0; a < current.satisfyingassignments; a++) {
    current.truthtable[a] = 1;
  }
  current.assignments = createAssignments();

  // create objects for storing the combinations, clauses, and the instance
  current.combinations = {};
  current.clauses = {};
  current.instance = {};

  // fill these objects, add UI elements
  for(var k = 3; k > 0; k--) {
    // create combinations
    current.combinations[k] = getCombinations(k, current.n);

    // fill current.instance with 0s
    current.instance[k] = [];
    for(var vg = 0; vg < current.combinations[k].length; vg++) {
      var temp = [];
      for(var cs = 0; cs < Math.pow(2, k); cs++) {
        temp.push(0);
      }
      current.instance[k].push(temp);
    }

    // create clauses
    current.clauses[k] = createClauses(k, current.combinations[k]);

    // add the tables with the clauses
    createClausesTable(k, current.n);
  }
  
  findTruthValues();

  if(current.showImpliedClauses) {
    findImpliedClauses();
  }

  updateClausesTable();
  
  createTruthTable(current.n);

  updateFormula();
})();

// Main functions

function clickCell(k, vg, cs) {
  var help = document.getElementById('help-clause' + k);

  // add/remove from current.instance
  if(current.instance[k][vg][cs] == 0 || current.instance[k][vg][cs] == 2) {
    current.instance[k][vg][cs] = 1;
    help.innerHTML = getClauseWithLetters(current.clauses[k][vg][cs]) + ' was added';
  }
  else if(current.instance[k][vg][cs] == 1) {
    current.instance[k][vg][cs] = 0;
    help.innerHTML = getClauseWithLetters(current.clauses[k][vg][cs]) + ' was removed';
  }
  update();
}

function clearClausesAll(k) {
  for(var vg = 0; vg < current.instance[k].length; vg++) {
    for(var cs = 0; cs < Math.pow(2, k); cs++) {
      current.instance[k][vg][cs] = 0;
    }
  }
  update();
}

function update() {
  updateFormula();

  findTruthValues();
  updateTruthTable();

  if(current.showImpliedClauses) {
    findImpliedClauses();
  }

  updateClausesTable();
}

function getFormula() {
  // create an array from current.instance that contains
  // only the clauses that are part of the formula  
  var formula = [];

  for(var k = 1; k <= 3; k++) {
    for(var vg = 0; vg < current.instance[k].length; vg++) {
      for(var cs = 0; cs < current.instance[k][vg].length; cs++) {
        if(current.instance[k][vg][cs] == 1) {
          formula.push(current.clauses[k][vg][cs]);
        }
      }
    }
  }
  return formula;
}

function findTruthValues() {
  var formula = getFormula();

  current.satisfyingassignments = Math.pow(2, current.n);

  // test all possible assignments
  for(var a = 0; a < Math.pow(2, current.n); a++) {
    if(checkAssignment(a, formula)) {
      current.truthtable[a] = 1;
    }
    else {
      current.truthtable[a] = 0;
      current.satisfyingassignments--;
    }
  }
}

function updateFormula() {
  var html = '&phi; = ';

  // collect the clauses into an array
  // that's similiar to getFormula() but
  // 1) clauses are in a reverse order (k = 3,2,1) 
  // 2) clauses are processed with getClauseWithLetters()
  var formula = [];
  for(var k = 3; k > 0; k--) {
    for(var vg = 0; vg < current.instance[k].length; vg++) {
      for(var cs = 0; cs < current.instance[k][vg].length; cs++) {
        if(current.instance[k][vg][cs] == 1) {
          formula.push(getClauseWithLetters(current.clauses[k][vg][cs]));
        }
      }
    }
  }

  if(formula.length === 0) {
    html += '&empty; (an empty formula with no clauses)';
  }
  else {
    html += formula.join(' &and; ');
  }

  document.getElementById('formula').innerHTML = html;
}

function checkAssignment(assignment, formula) {
  // loop through all clauses in the formula provided
  loopClauses:
  for(var c = 0; c < formula.length; c++) {
    // check if any of the literals in the clause evaluates to true
    for(var l = 0; l < formula[c].length; l++) {
      if(formula[c][l] == current.assignments[assignment][Math.abs(formula[c][l])-1]) {
        continue loopClauses;
      }
    }
    // none of the literals evaluates to true with current assignment
    // so the clause is not satisfied and so this particular assignment
    // does not satisfy the formula
    return false;
  }
  return true;
}

function findImpliedClauses() {
  var formula;

  // loop through all clauses
  for(var k = 1; k <= 3; k++) {
    for(var vg = 0; vg < current.instance[k].length; vg++) {
      loopClauses:
      for(var cs = 0; cs < current.instance[k][vg].length; cs++) {
        // skip clauses that are part of the formula
        if(current.instance[k][vg][cs] == 1) continue;

        // create formula from the clause to be tested
        formula = [];
        formula.push(current.clauses[k][vg][cs]);

        // and check the assignments
        for(var a = 0; a < current.truthtable.length; a++) {
          // test only the satisfying assignments
          if(current.truthtable[a] == 0) continue;

          // the clause is not implied if an assignment fails
          if(!checkAssignment(a, formula)) {
            current.instance[k][vg][cs] = 0;
            continue loopClauses;
          }

        }
        // the clause is implied if none of the assignments fail
        current.instance[k][vg][cs] = 2;
      }
    }
  }
}

// UI-related functions

function togglePopup() {
  var popup = document.getElementById('popup');
  if(popup.style.display == 'none') {
    popup.style.display = '';
  }
  else {
    popup.style.display = 'none';
  }
  return false;
}

function createTruthTable(n) {
  var html = '';
  html += '<table>';

  for(var row = 0; row <= n; row++) {
    html += '<tr>';

    // add first column (letters and phi)
    if(row < n) html += '<td class="header">' + letters[row] + '</td>';
    else html += '<td class="header phi">&phi;</td>';

    // add some extra space between the header and the assignments
    if(row == 0) {
      html += '<td rowspan="' + n + '"></td>';
    }
    if(row == n) {
      html += '<td class="phi"></td>';
    }
    
    for(var a = 0; a < Math.pow(2, n); a++) {
      // add the 2^n assignments
      if(row < n) {
        html += '<td id="assignment-' + a + '-' + row + '">';
        html += (a & (1 << (n - row - 1))) ? '1' : '0';
        html += '</td>';
      }
      // add the 2^n truth values
      else {
        html += '<td class="phi" id="truth-value-' + a + '">';
        html += current.truthtable[a] ? '1' : '0';
        html += '</td>';
      }
    }
    html += '</tr>';
  }

  html += '<tr>';
  html += '<td colspan="' + (Math.pow(2, current.n) + 2) +
    '" id="help-assignment" class="help">';
  html += '</td>';
  html += '</tr>';

  html += '</table>';

  document.getElementById('truthtable').innerHTML = html;

  updateSatisfyingAssignments();

  // set background color for 1s
  var element;  
  for(var a = 0; a < Math.pow(2, n); a++) {
    if(current.truthtable[a] == 1) {
      element = document.getElementById('truth-value-' + a);
      element.style.backgroundColor = colors.grey;    
    }
  }

  // set up event handlers
  for(var a = 0; a < Math.pow(2, n); a++) {
    for(var i = 0; i < current.n; i++) {
      element = document.getElementById('assignment-' + a + '-' + i);
      element.addEventListener('mouseover', selectionTruthTable.bind(this, a, true), false);
      element.addEventListener('mouseout', selectionTruthTable.bind(this, a, false), false);
    }

    element = document.getElementById('truth-value-' + a);
    element.addEventListener('mouseover', selectionTruthTable.bind(this, a, true), false);
    element.addEventListener('mouseout', selectionTruthTable.bind(this, a, false), false);
  }
}

function selectionTruthTable(assignment, show) {
  var element;
  var help = document.getElementById('help-assignment');
  
  // set text
  if(show) {
    help.innerHTML = getAssignmentWithLetters(assignment) + ' '
      + (current.truthtable[assignment] == 1 ? 'satisfies' : 'does not satisfy') +
      ' the formula';
  }
  else {
    help.innerHTML = '';
  }

  // set background colors
  for(var i = 0; i < current.n; i++) {
    element = document.getElementById('assignment-' + assignment + '-' + i);
    element.style.backgroundColor = show ? colors.grey : colors.white;
  }
}

function updateTruthTable() {
  var element;

  for(var a = 0; a < current.truthtable.length; a++) {
    element = document.getElementById('truth-value-' + a);
    element.innerHTML = current.truthtable[a];

    if(current.truthtable[a] == 1) {
      element.style.backgroundColor = colors.grey;
    }
    else {
      element.style.backgroundColor = colors.white;
    }
  }

  updateSatisfyingAssignments();
}

function updateSatisfyingAssignments() {
  var string = current.satisfyingassignments + ' satisfying assignment';

  if(current.satisfyingassignments > 1) {
    string += 's';
  }

  document.getElementById('satisfying-assignments').innerHTML = string;
}

function getAssignmentWithLetters(a) {
  var assignment = [];
  var letter;
  for(var i = 0; i < current.n; i++) {
    letter = letters[Math.abs(current.assignments[a][i])-1];
    
    if(current.assignments[a][i] > 0) {
      assignment.push(letter);
    }
    else {
      assignment.push('-' + letter);
    }
  }

  return '{ ' + assignment.join(', ') + ' }';
}

function getClauseWithLetters(c) {
  var clause = [];
  var letter;
  
  for(var i = 0; i < c.length; i++) {
    letter = letters[Math.abs(c[i])-1];
    if(c[i] > 0) {
      clause.push(letter);
    }
    else {
      clause.push('-' + letter);
    }
  }

  if(clause.length == 1) {
    return clause[0];
  }
  else {
    return '(' + clause.join(' &or; ') + ')';
  }
}

function createClausesTable(k, n) {
  var html = '';

  html += '<table class="clauses">';

  // create a header that contains the variable groups
  html += '<tr>';
  html += '<td class="clear" id="clear' + k + '"></td>';
  for(var column = 0; column < current.combinations[k].length; column++) {
    html += '<td class="vg">';
    html += getCombinationWithLetters(current.combinations[k][column]);
  }
  html += "</tr>";

  for(var row = 0; row < Math.pow(2, k); row++) {
    html += '<tr>';

    html += '<td style="width: 40px;">' + convertDecimalToBinaryWithPadding(row, k) + ' </td>';

    for(var column = 0; column < current.combinations[k].length; column++) {
      html += '<td class="clause" id="cell-' + k + '-' + column + '-' + row + '"></td>';
    }
    html += '</tr>';
  }

  html += '<tr>';
  html += '<td colspan="' + (current.combinations[k].length + 1) +
    ' "id="help-clause' + k + '" class="help"></td>';
  html += '</tr>';

  html += '</table>';

  document.getElementById('clauses' + k).innerHTML = html;

  // add event listeners
  var element;
  for(var vg = 0; vg < current.combinations[k].length; vg++) {
    for(var cs = 0; cs < Math.pow(2, k); cs++) {
      element = document.getElementById('cell-' + k + '-' + vg + '-' + cs);
      element.addEventListener('click', clickCell.bind(this, k, vg, cs), false);
      element.addEventListener('mouseover', selectionClausesTable.bind(this, k, vg, cs, true), false);
      element.addEventListener('mouseout', selectionClausesTable.bind(this, k, vg, cs, false), false);
    }
  }

  element = document.getElementById('clear' + k);
  element.addEventListener('click', clearClausesAll.bind(this, k), false);
}

function selectionClausesTable(k, vg, cs, show) {
  var cell = document.getElementById('cell-' + k + '-' + vg + '-' + cs);
  var help = document.getElementById('help-clause' + k);

  if(show) {
    cell.style.backgroundColor = colors.black;

    if(current.instance[k][vg][cs] == 0 || current.instance[k][vg][cs] == 2) {
      help.innerHTML = 'add ' + getClauseWithLetters(current.clauses[k][vg][cs]);
    }
    else {
      help.innerHTML = 'remove ' + getClauseWithLetters(current.clauses[k][vg][cs]);
    }    
  }
  else {
    switch(current.instance[k][vg][cs]) {
      case 0:
        cell.style.backgroundColor = colors.white;
        break;
      case 1:
        cell.style.backgroundColor = colors.black;
        break;
      case 2:
        if(current.showImpliedClauses) {
          cell.style.backgroundColor = colors.grey;
        }
        else {
          cell.style.backgroundColor = colors.white;
        }
        break;
    }
    help.innerHTML = '';
  }  
}

function updateClausesTable() {
  var element;
  for(var k = 1; k <= 3; k++) {
    for(var vg = 0; vg < current.instance[k].length; vg++) {
      for(var cs = 0; cs < current.instance[k][vg].length; cs++) {
        element = document.getElementById('cell-' + k + '-' + vg + '-' + cs);
        switch(current.instance[k][vg][cs]) {
          case 0:
            element.style.backgroundColor = colors.white;
            break;
          case 1:
            element.style.backgroundColor = colors.black;
            break;
          case 2:
            if(current.showImpliedClauses) {
              element.style.backgroundColor = colors.grey;
            }
            break;
        }
      }
    }
  }
}

function toggleImpliedClauses() {
  // invert the current value of showImpliedClauses
  current.showImpliedClauses = !current.showImpliedClauses;
  
  if(current.showImpliedClauses) {
    findImpliedClauses();
    updateClausesTable();
  }
  else {
    // update backgrounds of the cells to white
    var element;
    for(var k = 1; k <= 3; k++) {
      for(var vg = 0; vg < current.instance[k].length; vg++) {
        for(var cs = 0; cs < Math.pow(2, k); cs++) {
          if(current.instance[k][vg][cs] != 2) continue;
          if(!current.showImpliedClauses) {
            element =  document.getElementById('cell-' + k + '-' + vg + '-' + cs);
            element.style.backgroundColor = colors.white;
          }
        }
      }
    }
  }
}

// Utilities
// returns an array containing the elements of C(k, n) in colexicographic order
function getCombinations(k, n) {
  var combinations = [];
  var temp;

  // create the first combination (k number of 1s)
  var combination = Math.pow(2, k) - 1;

  while(combination < Math.pow(2, n)) {
    temp = [];

    for(var j = n; j > 0; j--) {
      if((combination & (1 << j - 1)) != 0) {
        temp.unshift(j);
      }
    }

    combinations.push(temp);
    // generate the next combination
    combination = hakmem175(combination);
  }
  return combinations;
}

// source: http://code.stephenmorley.org/articles/hakmem-item-175/
function hakmem175(value) {
  var lowestBit = value & -value;
  var leftBits = value + lowestBit;
  var changedBits = value ^ leftBits;
  var rightBits = (changedBits / lowestBit) >>> 2;
  return (leftBits | rightBits);
}

function createAssignments() {
  var temp;
  var assignments = [];

  for(var a = 0; a < Math.pow(2, current.n); a++) {
    temp = [];
    for(var i = 0; i < current.n; i++) {
      if((a & 1 << (current.n-1-i)) == 0) {
        temp.push((i+1)*-1);
      }
      else {
        temp.push(i+1);
      }
    }
    assignments.push(temp);
  }
  return assignments;
}

function createClauses(k, combinations) {
  var clauses = [];
  var clause;

  for(var vg = 0; vg < combinations.length; vg++) {
    clauses[vg] = [];
    for(var cs = 0; cs < Math.pow(2, k); cs++) {
      clause = [];
      for(var i = k - 1; i >= 0; i--) {
        if (cs & 1 << i) {
          clause.push(combinations[vg][k - 1 - i]);
        }
        else {
          clause.push(combinations[vg][k - 1 - i] * -1);
        }
      }
      clauses[vg].push(clause);
    }
  }
  return clauses;
}

function convertDecimalToBinaryWithPadding(decimal, length) {
  var binary = decimal.toString(2);

  while(binary.length < length) {
    binary = '0' + binary;
  }

  return binary;
}

// [1, 2, 3] (array) -> "abc" (string)
function getCombinationWithLetters(combination) {
  var c = '';

  for(var i = 0; i < combination.length; i++) {
    c += letters[combination[i] - 1];
  }

  return c;
}