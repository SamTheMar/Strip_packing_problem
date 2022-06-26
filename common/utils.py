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
    wt : int
        size of the width of the strip
    n : int
        number of rectangles
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    """
    with open(filename, "r") as f:
        content = f.read()

    lines = content.split("\n")
    wt = int(lines[0].split(" ")[0])
    n = int(lines[1].split(" ")[0])

    cont = np.asarray([lines[i+2].split(" ") for i in range(n)], dtype=int)

    rectangles = [Rectangle(cont[i, 0], cont[i, 1]) for i in range(len(cont))]

    return wt, n, rectangles
    

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
    wt : int
        size of the width of the strip
    ht : int
        size of the height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    with open(filename, "r") as f:
        content = f.read()

    lines = content.split("\n")
    wt, ht = (int(x) for x in lines[0].split(" "))
    n = int(lines[1].split(" ")[0])

    cont = np.asarray([lines[i+2].split(" ") for i in range(n)], dtype = int)
    
    rectangles = [PositionedRectangle(cont[i, 2], cont[i, 3], cont[i, 0], cont[i, 1]) for i in range(len(cont))]
    
    return wt, ht, rectangles


def visualize(width, height, rectangles, ax = None, plot_width = -1):
    """
    Visualization of the a strip of size width x height with the layout of the rectangles.
    The rectangles are annotated with their place in the input list on the figure.

    Parameters
    ----------
    width : number
        size of the width of the strip
    height : number
        size of the height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    ax : ``matplotlib.axes._subplots.AxesSubplot``, optional
        The axes on which to show the plot
    plot_width : int, default 720
        Plot height in pixels.

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    linewidth = 3
    if ax == None:
        if plot_width == -1:
            plot_width = 720

        aspect = height/width
        fw, fh, dpi = plot_width, plot_width*aspect, 100
        fig, ax = plt.subplots(figsize = (fw/dpi, fh/dpi), dpi = dpi)

    else:
        fig = ax.get_figure()

    ax.add_patch(
        patches.Rectangle(
            (0, 0),  # (x,y)
            width,  # width
            height,  # height
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
                linewidth = linewidth
            )
        )
        ax.text(r.x + 0.25, r.y + 0.25, str(idx+1), fontsize = 'xx-large')

    ax.set_xlim(0, width)
    ax.set_ylim(0, height)

    ax.set_xticks(np.arange(width))
    ax.set_yticks(np.arange(height))

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

    kwargs
        keyowrd arguments passed to ``visualize``

    Returns
    -------
    ``matplotlib.figure.Figure``, ``matplotlib.axes._subplots.AxesSubplot``
    """
    fig, ax = visualize(*read_solution(filename), **kwargs)
    return fig, ax
