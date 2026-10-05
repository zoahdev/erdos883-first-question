import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_92 :
    (List.ofFn coreChunks680_92).flatten =
      (coreData680.take (coreResources680 92).q).drop 172 := by
  decide +kernel

theorem coreCheck680_92 :
    ∀ c : Fin 1, (coreChunks680_92 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 92)) = true := by
  decide +kernel
#print axioms coreFlatten680_92
#print axioms coreCheck680_92
end Erdos883Verified
