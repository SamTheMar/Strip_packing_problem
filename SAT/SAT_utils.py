
def order_encode(value, vmin = 0, vmax = -1):
    """
    Parameters
    ----------
    value : int
        value to encode
    vmin : int, defualt 0
        starting value of the domain
    vmax : int, optional
        final value of the domain. Defaults to value

    Returns
    -------
    list of bool
        the order encoded value in the form [False, ..., False, True, True, ...]
    """
    if vmax < value:
        if vmax != -1:
            print("Attention! The given length of the encoding is smaller than the value to encode!")
        vmax = value
    
    if value < vmin:
        print("Attention! The encoded value is smaller than the minimum value of the domain!")


    encoding = []
    for i in range(vmin, vmax):
        encoding.append(value <= i)
    return encoding


def order_decode(encoding, vmin = 0):
    """
    Parameters
    ----------
    encoding : list of bool
        order encoded value in the form [False, ..., False, True, True, ...]
    vmin : int, default 0
        starting value of the domain of the encoded value

    Returns
    -------
    int
        the decoded value
    """
    for i, val in enumerate(encoding):
        if val:
            return i + vmin
    return len(encoding) + vmin