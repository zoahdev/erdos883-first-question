import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_83 :
    (List.ofFn coreChunks509_83).flatten =
      (coreData509.take (coreResources509 83).q).drop 168 := by
  decide +kernel

theorem coreCheck509_83 :
    ∀ c : Fin 1, (coreChunks509_83 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 83)) = true := by
  decide +kernel
#print axioms coreFlatten509_83
#print axioms coreCheck509_83
end Erdos883Verified
