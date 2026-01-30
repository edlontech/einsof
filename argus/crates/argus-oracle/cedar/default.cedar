permit(
    principal,
    action == Argus::Action::"invoke",
    resource
) when {
    resource.endorsed == true
};
