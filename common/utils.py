import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches
import matplotlib.colors as mcolors

from collections import namedtuple

PositionedRectangle = namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
Rectangle = namedtuple('Rectangle', ['w', 'h'])

def read_instance(filename):
    """
    Parameters
    ----------
    filename : string
        file of the instance. Its format is:
        total_width
        n_rectangles
        w_1 h_1
        ......
        w_n h_n

    Returns
    -------
    W : int
        total width of the strip
    n : int
        number of rectangles
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    """
    with open(filename, "r") as f:
        content = f.read()

    lines = content.split("\n")
    W = int(lines[0].split(" ")[0])
    n = int(lines[1].split(" ")[0])

    cont = np.asarray([lines[i+2].split(" ") for i in range(n)], dtype=int)

    rectangles = [Rectangle(cont[i, 0], cont[i, 1]) for i in range(len(cont))]

    return W, n, rectangles
    

def read_solution(filename):
    """
    Parameters
    ----------
    filename : string
        file of the solution. Its format is:
        total_width total_height
        n_rectangles
        w_1 h_1 x_1 y_1
        ......
        w_n h_n x_n y_n

    Returns
    -------
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    with open(filename, "r") as f:
        content = f.read()

    lines = content.split("\n")
    W, H = (int(x) for x in lines[0].split(" "))
    n = int(lines[1].split(" ")[0])

    cont = np.asarray([lines[i+2].split(" ") for i in range(n)], dtype = int)
    
    rectangles = [PositionedRectangle(cont[i, 2], cont[i, 3], cont[i, 0], cont[i, 1]) for i in range(len(cont))]
    
    return W, H, rectangles


def save_solution(filename, W, H, rectangles):
    """
    Parameters
    ----------
    filename : string
        absolute or relative path of the solution file
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    with open(filename, "w") as f:
        f.write(f"{W} {H}\n")
        f.write(f"{len(rectangles)}\n")

        for rect in rectangles:
            f.write(f"{rect.w} {rect.h} {rect.x} {rect.y}\n")


def visualize(W, H, rectangles, ax = None, plot_width = -1):
    """
    Visualization of the a strip of size width x height with the layout of the rectangles.
    The rectangles are annotated with their place in the input list on the figure.

    Parameters
    ----------
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    ax : ``matplotlib.axes._subplots.AxesSubplot``, optional
        The axes on which to show the plot
    plot_width : int, default 720
        Plot width in pixels.

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    linewidth = 3
    if ax == None:
        if plot_width == -1:
            plot_width = 720

        aspect = H/W
        fw, fh, dpi = plot_width, plot_width*aspect, 100
        fig, ax = plt.subplots(figsize = (fw/dpi, fh/dpi), dpi = dpi)

    else:
        fig = ax.get_figure()

    ax.add_patch(
        patches.Rectangle(
            (0, 0),  # (x,y)
            W,  # width
            H,  # height
            hatch='x',
            fill=False,
        )
    )

    colors = list(mcolors.TABLEAU_COLORS.values())

    for idx, r in enumerate(rectangles):
        ax.add_patch(
            patches.Rectangle(
                (r.x, r.y),  # (x,y)
                r.w,  # width
                r.h,  # height
                facecolor = colors[idx%10],
                edgecolor = 'k',
                linewidth = linewidth,
                alpha = 0.8
            )
        )
        ax.text(r.x + 0.25, r.y + 0.25, str(idx+1), fontsize = 'xx-large')

    ax.set_xlim(0, W)
    ax.set_ylim(0, H)

    ax.set_xticks(np.arange(W))
    ax.set_yticks(np.arange(H))

    ax.set_aspect('equal', adjustable='box')

    ax.grid(color = 'k', ls = '--')
    ax.set_facecolor('w')

    for b in ax.spines.values():
        b.set_linewidth(linewidth)

    fig.tight_layout()

    return fig, ax


def visualize_from_file(filename, **kwargs):
    """
    Visualization of the a strip of size width x height with the layout of the rectangles.
    The rectangles are annotated with their place in the input list on the figure.
    Parameters
    ----------
    filename : string
        file of the solution. Its format is:
        total_width total_height
        n_rectangles
        w_1 h_1 x_1 y_1
        ......
        w_n h_n x_n y_n
    kwargs : dict
        keyowrd arguments passed to ``visualize``

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    fig, ax = visualize(*read_solution(filename), **kwargs)
    return fig, ax
