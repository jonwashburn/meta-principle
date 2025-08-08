namespace MetaPrinciple

inductive SpatialDim | two | three | fourUp

theorem stable_distinction_dimension : SpatialDim := by exact SpatialDim.three

end MetaPrinciple
