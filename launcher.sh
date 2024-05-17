#!/bin/bash

# Utility
is_in() {
    local element="$1"
    shift
    local array=("$@")
    for item in "${array[@]}"; do
        if [[ "$item" == "$element" ]]; then
            return 0 
        fi
    done
    return 1 
}

# Comparators used to check 
# TODO : tenere aggiornato
valid_solvers=("chuffed" "gecode")
valid_approaches=("CP" "MIP" "SAT" "SMT")

# Print options 
echo "In order to execute the models, choose at least one element for category:"
echo "1) Instances: inst1, ..., inst21"
echo "2) Solvers: [chuffed, gecode]"
echo "3) Approaches: [CP, MIP, SAT, SMT]"

while true; do

    # Ask for instances + checks
    echo "insert instance/s number/s among 1 and 21: "
    read -a instances
    for i in "${instances[@]}"; do 
        if ! [[ "$i" -ge 1 && "$i" -le 21 ]]; then
            echo "Invalid instance: $i."
            read -a instances
            continue 2
        fi
    done

    echo "insert solver/s name (choose among chuffed, gecode): " # TODO : tenere aggiornato
    read -a solvers
    for s in "${solvers[@]}"; do 
        if ! is_in "$s" "${valid_solvers[@]}"; then
            echo "Invalid solver: $s."
            read -a solvers
            continue 2
        fi
    done
    
    echo "insert approach/es name/s (choose among CP, MIP, SAT, SMT): " # TODO : tenere aggiornato
    read -a approachs
    for a in "${approaches[@]}"; do
        if ! is_in "$a" "${valid_approaches[@]}"; then
            echo "Invalid approach: $a."
            read -a approachs
            continue 2
        fi
    done

    # Execute instances
    for method in "${approachs[@]}"; do
        for solver in "${solvers[@]}"; do
            for instance in "${instances[@]}"; do
                echo "Executing inst$instance by $solver with $method..."
                case "$method" in
                    "CP")
                        # TODO : implementare metodo
                        ;;
                    "MIP")
                        # TODO : implementare metodo
                        ;;
                    "SAT")
                        # TODO : implementare metodo
                        ;;
                    "SMT")
                        # TODO : implementare metodo
                        ;;
                esac
            done
        done
    done

    echo "Do you want to continue with one other execution? (y/n)"
    read continue_choice

    if [[ "$continue_choice" != "y" ]]; then
        echo "Execution completed."
        break
    fi
done