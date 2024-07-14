# Settings synchronization

This model describes an algorithm to synchronize the settings of a device.

Settings can be changed both locally and remotely. Moreover, a device can get
offline at any moment. When offline, (requests of) remote changes are stored in
a intermediate network entity (a "shadow") and are applied when device gets back
online. However, the settings can also have been locally changed on the device
while it was offline. Therefore, a conflict resolution mechanism is needed to
handle the settings that have been changed both locally and remotely. The chosen
policy is that the newest change is always applied. This implies that the date a
change is made at (locally) or requested at (remotely) is known. This also
implies that the device and the remote entity share a common clock.

When the device is online, remote changes are considered immediately applied. In
reality, there could be a delay between the date the change is remotely
requested at and the date it is applied at. In any case, the newest change is
applied, so this doesn't impact the overall logic.

The model also consider that the device can be shut down and rebooted at any
moment.

The main notion used in this model is that of a configuration. A configuration
is a set of settings with their values and request dates. For a change request
to be considered a configuration, configuration are allowed to be partial. This
means that some settings can be missing in a configuration, i.e. they have no
value.

Applying a change is then applying a configuration onto another. The former
represents the request (what must be changed) and the latter the configuration
in use. We say the configurations are merged. The resulting merged configuration
has the newest values for each settings (a missing setting is always considered
older).

A reflexive order is defined on configurations: a configuration A is before or
equal to a configuration B iff all A's settings are before or equal to
corresponding B's settings.

Several configurations exist simultaneously:

- the device configuration: the local configuration currently used by the device

- the desired configuration: a configuration stored in the "shadow" that
  represents remotely requested changes. This configuration is not necessarily
  already merged with the device configuration, because the device can be
  offline.

- the reported configuration: a configuration stored in the "shadow" that
  mirrors the local device configuration. It may be out of date due to the
  device being offline.

The main invariant the synchronization algorithm must respect is:

- If the device is online, the desired configuration is always before or equal
  to the device configuration. This means that the desired configuration has
  been merged (recall that when the device is online, remote changes are applied
  immediately).

Other invariants are:

- The reported configuration is always before or equal to the device
  configuration.

- No configuration is in the future, i.e. no setting can be associated to a date
  after now.

The dynamic events the model describes are:

- the device boots
- the device shuts down
- the device gets online
- the device gets offline
- a setting is locally changed on the device
- a setting change is remotely requested
- the device reports its settings

Definitions are followed by proofs of their properties. These proofs are then
used by invariant proofs.

Since everything is proved, the checker is mostly irrelevant. See however the
checker configuration for an instantiation example of the constants.

The model is best viewed with an editor handling font ligatures, such as the
["TLA+ Toolbox" IDE](https://github.com/tlaplus/tlaplus/releases/download/v1.7.1/TLAToolbox-1.7.1-linux.gtk.amd64.deb).

A good starting font is [FiraCode](https://github.com/tonsky/FiraCode).
