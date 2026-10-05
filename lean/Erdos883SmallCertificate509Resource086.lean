import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_86 :
    (List.ofFn coreChunks509_86).flatten =
      (coreData509.take (coreResources509 86).q).drop 196 := by
  decide +kernel

theorem coreCheck509_86 :
    ∀ c : Fin 1, (coreChunks509_86 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 86)) = true := by
  decide +kernel
#print axioms coreFlatten509_86
#print axioms coreCheck509_86
end Erdos883Verified
