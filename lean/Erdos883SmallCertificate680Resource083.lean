import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_83 :
    (List.ofFn coreChunks680_83).flatten =
      (coreData680.take (coreResources680 83).q).drop 152 := by
  decide +kernel

theorem coreCheck680_83 :
    ∀ c : Fin 1, (coreChunks680_83 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 83)) = true := by
  decide +kernel
#print axioms coreFlatten680_83
#print axioms coreCheck680_83
end Erdos883Verified
