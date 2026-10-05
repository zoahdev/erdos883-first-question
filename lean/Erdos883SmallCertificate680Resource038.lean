import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_38 :
    (List.ofFn coreChunks680_38).flatten =
      (coreData680.take (coreResources680 38).q).drop 158 := by
  decide +kernel

theorem coreCheck680_38 :
    ∀ c : Fin 1, (coreChunks680_38 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 38)) = true := by
  decide +kernel
#print axioms coreFlatten680_38
#print axioms coreCheck680_38
end Erdos883Verified
