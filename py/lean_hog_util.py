def checked_invariant_value(inv_type, val_str):
    value = None
    if val_str in ['undefined', 'Computation time out', 'Computing']:
        value = None
    else:        
        if inv_type == 'bool':
            if val_str in ['Yes', 'No']: # valid bool values
                value = val_str == 'Yes'
            else:
                raise ValueError # fail early
        elif val_str == 'infinity': # for now, ok for ints and floats
            value = 'infinity'
        elif inv_type == 'int':
            value = int(val_str)
        elif inv_type == 'float':
            value = float(val_str)
        else:
            raise ValueError # fail early
    return value