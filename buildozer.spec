[app]

title = Moh_sud game
package.name = Moahmmed_app
package.domain = org.example

source.dir = .
source.include_exts = py,png,jpg,jpeg,kv,atlas

version = 0.1

requirements = python3,kivy

orientation = portrait
fullscreen = 0

android.archs = arm64-v8a
android.minapi = 24
android.api = 36
android.ndk = 29
android.accept_sdk_license = True

p4a.branch = develop

[buildozer]

log_level = 2
warn_on_root = 1
