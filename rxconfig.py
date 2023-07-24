"""
TODO: Evidently, I'm able to modify config settings here, but who knows?
"""
import reflex as rx


class DeriverConfig(rx.Config):
    """
    TODO: Find out what the fuck this thing does.
    """


config = DeriverConfig(
    app_name="Deriver",
    db_url="sqlite:///reflex.db",
    env=rx.Env.DEV,
)
