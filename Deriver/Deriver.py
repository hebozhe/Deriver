"""Welcome to Reflex! This file outlines the steps to create a basic app."""
from bzns.primitives import SYM_CONV
import reflex as rx
from rxconfig import config

docs_url: str = "https://reflex.dev/docs/getting-started/introduction"
filename: str = f"{config.app_name}/{config.app_name}.py"


class State(rx.State):
    """The app state."""


def index() -> rx.Component:
    """
    This function houses the frontend components for the homepage.
    """
    return rx.fragment(
        rx.color_mode_button(rx.color_mode_icon(), float="right"),
        rx.vstack(
            rx.heading("Welcome to Reflex!", font_size="2em"),
            rx.box("Get started by editing ", rx.code(filename, font_size="1em")),
            rx.link(
                "Check out our docs!",
                href=docs_url,
                border="0.1em solid",
                padding="0.5em",
                border_radius="0.5em",
                _hover={
                    "color": rx.color_mode_cond(
                        light="rgb(107,99,246)",
                        dark="rgb(179, 175, 255)",
                    )
                },
            ),
            spacing="1.5em",
            font_size="2em",
            padding_top="10%",
        ),
    )


# Add state and page to the app.
app = rx.App(state=State)
app.add_page(index)
app.compile()
