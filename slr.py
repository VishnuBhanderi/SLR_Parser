import streamlit as st
import graphviz

EPSILON = 'EPS'


def read_grammar(filename):
    with open(filename, 'r') as file:
        lines = file.readlines()

    terminals = []
    non_terminals = []

    for line in lines:
        line = line.strip()
        if line.startswith("TERMINALS"):
            terminals = line.split()[1:]
        elif line.startswith("NONTERMINALS"):
            non_terminals = line.split()[1:]
        elif line == '##':
            break

    productions = {}
    for line in lines:
        line = line.strip()
        if '->' in line:
            left, right = line.split(' -> ')
            non_terminal = left.strip()
            if non_terminal in non_terminals:  # Only add if non-terminal is in non_terminals
                production_rules = [rule.strip() for rule in right.split('|')]
                productions[non_terminal] = production_rules

    print("Productions:")
    for key, value in productions.items():
        print(key, ":", value)

    return terminals, non_terminals, productions

def compute_first_sets(non_terminals, terminals, productions):
    first_sets = {non_terminal: set() for non_terminal in non_terminals}

    # Helper function to compute FIRST set of a symbol
    def compute_first(symbol, visited=None):
        if visited is None:
            visited = set()
        if symbol in terminals:
            return {symbol}
        if symbol in visited:
            return set()
        visited.add(symbol)
        first_set = set()
        for production in productions[symbol]:
            first_symbol = production[0]
            if first_symbol in terminals:
                first_set.add(first_symbol)
            elif first_symbol in non_terminals:
                first_set |= compute_first(first_symbol, visited)
        return first_set

    # Compute FIRST sets for all non-terminals
    for non_terminal in non_terminals:
        first_sets[non_terminal] |= compute_first(non_terminal)

    return first_sets

def compute_follow_sets(non_terminals, terminals, productions, start_symbol):
    first_sets = compute_first_sets(non_terminals, terminals, productions)
    follow_sets = {non_terminal: set() for non_terminal in non_terminals}
    follow_sets[start_symbol].add('$')  # $ represents end of input

    # Helper function to compute FOLLOW set of a non-terminal symbol
    def compute_follow(symbol, visited=None):
        if visited is None:
            visited = set()
        if symbol in visited:
            return set()
        visited.add(symbol)
        follow_set = set()
        for non_terminal, production_list in productions.items():
            for production in production_list:
                if symbol in production:
                    idx = production.index(symbol)
                    if idx < len(production) - 1:
                        next_symbol = production[idx + 1]
                        if next_symbol in terminals:
                            follow_set.add(next_symbol)
                        elif next_symbol in non_terminals:
                            follow_set |= first_sets[next_symbol]
                            if EPSILON in follow_set:
                                follow_set.remove(EPSILON)  # Removing epsilon from FOLLOW set
                            if EPSILON in first_sets[next_symbol]:
                                # If epsilon is in the FIRST set of the next symbol,
                                # consider the FOLLOW set of the current non-terminal
                                follow_set |= compute_follow(next_symbol, visited)
                    else:
                        # If the current symbol is the last one in the production,
                        # consider the FOLLOW set of the current non-terminal
                        if non_terminal != symbol:
                            follow_set |= compute_follow(non_terminal, visited)
                        if symbol != non_terminal and '$' in follow_sets[non_terminal]:
                            follow_set |= follow_sets[non_terminal]  # Include end-of-input marker
        return follow_set

    # Compute FOLLOW sets for all non-terminals
    for non_terminal in non_terminals:
        follow_sets[non_terminal] |= compute_follow(non_terminal)

    return follow_sets

def construct_lr0_items(productions, non_terminals):
    lr0_items = []
    start_production = list(productions.keys())[0]
    start_item = (start_production, tuple(productions[start_production][0]), 0)
    lr0_items.append(closure([start_item], productions, non_terminals))
    augmented_production = ('S\'', (start_production,), 0)  # Augmented production
    lr0_items[0] = lr0_items[0].union({augmented_production})  # Union with the augmented production
    i = 0
    while i < len(lr0_items):
        current_state = lr0_items[i]
        next_symbols = get_next_symbols(current_state, productions)
        for symbol in next_symbols:
            goto_state = goto(current_state, symbol, productions, non_terminals)
            if goto_state and goto_state not in lr0_items:
                lr0_items.append(goto_state)
        i += 1
    return lr0_items

def closure(lr0_items, productions, non_terminals):
    closure_set = set(lr0_items)
    added = True
    while added:
        added = False
        for item in list(closure_set):
            production, production_rule, dot_position = item
            if dot_position < len(production_rule) and production_rule[dot_position] in non_terminals:
                for prod in productions[production_rule[dot_position]]:
                    new_item = (production_rule[dot_position], tuple(prod), 0)
                    if new_item not in closure_set:
                        closure_set.add(new_item)
                        added = True
    return frozenset(closure_set)

def goto(lr0_items, symbol, productions, non_terminals):
    goto_set = set()
    for item in lr0_items:
        production, production_rule, dot_position = item
        if dot_position < len(production_rule) and production_rule[dot_position] == symbol:
            goto_set.add((production, production_rule, dot_position + 1))
    return closure(goto_set, productions, non_terminals)

def get_next_symbols(lr0_items, productions):
    symbols = set()
    for item in lr0_items:
        production, production_rule, dot_position = item
        if dot_position < len(production_rule):
            symbols.add(production_rule[dot_position])
    return symbols

def generate_slr_parsing_table(terminals, non_terminals, lr0_items, productions, follow_sets):
    parsing_table = {}

    # Add '$' symbol to terminals
    terminals.append('$')

    # Initialize parsing table
    for i, lr0_state in enumerate(lr0_items):
        parsing_table[i] = {terminal: None for terminal in terminals}
        parsing_table[i].update({non_terminal: None for non_terminal in non_terminals})

    # Fill in the parsing table
    for i, lr0_state in enumerate(lr0_items):
        for item in lr0_state:
            production, production_rule, dot_position = item
            production_rule_str = ' '.join(production_rule)
            formatted_item = f"[ {production} -> {production_rule_str} ]"
            if dot_position < len(production_rule):
                symbol = production_rule[dot_position]
                if symbol in terminals:
                    goto_state = goto(lr0_state, symbol, productions, non_terminals)
                    j = lr0_items.index(goto_state)
                    parsing_table[i][symbol] = ('Shift', j)
                else:  # Symbol is in non-terminals
                    goto_state = goto(lr0_state, symbol, productions, non_terminals)
                    j = lr0_items.index(goto_state)
                    parsing_table[i][symbol] = ('',j)  # Update parsing_table with goto state index    
            else:
                if production == 'S\'':
                    parsing_table[i]['$'] = ('accept',)
                else:
                    follow_set = follow_sets[production]
                    for terminal in follow_set:
                        if terminal != EPSILON:  # Skip epsilon from follow sets
                            if parsing_table[i][terminal] is not None:
                                print("Conflict detected: Follow set conflict")
                                return None
                            parsing_table[i][terminal] = ('Reduce', formatted_item)

    return parsing_table

def print_parsing_table(parsing_table):
    print("Parsing Table:")
    headers = list(parsing_table[0].keys())  # Get all symbols as column headers
    table = [[""] + headers]  # Initialize table with headers
    for state, actions in parsing_table.items():
        row = [state]
        for symbol in headers:
            action = actions.get(symbol)  # Get the action for the symbol
            if action is None:
                row.append("")
            else:
                if len(action) == 2:  # Check if the action tuple contains two values
                    action_type, state = action
                    row.append(f"{action_type} {state}")
                else:
                    # If only one value is present, it must be 'accept'
                    row.append('accept')
        table.append(row)

def print_parsing_table(parsing_table):
    headers = list(parsing_table[0].keys())  # Get all symbols as column headers
    table = [["State"] + headers]  # Initialize table with headers
    for state, actions in parsing_table.items():
        row = [state]
        for symbol in headers:
            action = actions.get(symbol)  # Get the action for the symbol
            if action is None:
                row.append("")
            else:
                if len(action) == 2:  # Check if the action tuple contains two values
                    action_type, state = action
                    row.append(f"{action_type} {state}")
                else:
                    # If only one value is present, it must be 'accept'
                    row.append('accept')
        table.append(row)
    return table

def main():
    st.title('LR(0) Parser Generator')
    filename = "grammar.txt"
    # Sidebar
    st.sidebar.title("Options")
    show_lr0_items = st.sidebar.checkbox("Show LR(0) Item Sets")
    show_first_follow_sets = st.sidebar.checkbox("Show FIRST and FOLLOW Sets")
    show_parsing_table = st.sidebar.checkbox("Show Parsing Table")
    
    # Footer
    st.sidebar.markdown("---")
    st.sidebar.markdown("© 2024. All rights reserved. Vishnu Bhanderi.")

    # Main content
    terminals, non_terminals, productions = read_grammar(filename)
    start_symbol = non_terminals[0]
    first_sets = compute_first_sets(non_terminals, terminals, productions)
    follow_sets = compute_follow_sets(non_terminals, terminals, productions, start_symbol)
    lr0_items = construct_lr0_items(productions, non_terminals)

    if show_lr0_items:
        st.header('LR(0) Item Sets')
        graph = graphviz.Digraph()

        # Define custom node attributes for LR(0) item sets
        node_attributes = {
            'shape': 'ellipse',
            'style': 'bold, rounded',
            'fontname': 'helvetica',
            'fontsize': '12',
            'fontcolor': 'black',
        }

        for i, lr0_item in enumerate(lr0_items):
            closure_str = f'Item Set {i}:\n'
            for item in lr0_item:
                production, production_rule, dot_position = item
                closure_str += f"{production} -> "
                for j, symbol in enumerate(production_rule):
                    if j == dot_position:
                        closure_str += '.'
                    closure_str += symbol
                if dot_position == len(production_rule):
                    closure_str += '.'
                closure_str += '\n'
            # Add node with custom attributes
            graph.node(f'Item Set {i}', label=closure_str.strip(), **node_attributes)
        for i, lr0_item in enumerate(lr0_items):
            next_symbols = get_next_symbols(lr0_item, productions)
            for symbol in next_symbols:
                goto_state = goto(lr0_item, symbol, productions, non_terminals)
                j = lr0_items.index(goto_state)
                graph.edge(f'Item Set {i}', f'Item Set {j}', label=symbol)
        st.graphviz_chart(graph.source)

    if show_first_follow_sets:
        st.header('FIRST Sets')
        for symbol, first_set in first_sets.items():
            st.write(f"FIRST({symbol}) = {first_set}")

        st.header('FOLLOW Sets')
        for symbol, follow_set in follow_sets.items():
            st.write(f"FOLLOW({symbol}) = {follow_set}")

    if show_parsing_table:
        parsing_table = generate_slr_parsing_table(terminals, non_terminals, lr0_items, productions, follow_sets)
        if parsing_table:
            st.header('Parsing Table')
            table_data = print_parsing_table(parsing_table)
            st.table(table_data)


if __name__ == "__main__":
    main()