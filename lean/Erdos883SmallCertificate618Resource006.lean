import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_6 :
    (List.ofFn coreChunks618_6).flatten =
      (coreData618.take (coreResources618 6).q).drop 81 := by
  decide +kernel

theorem coreCheck618_6 :
    ∀ c : Fin 1, (coreChunks618_6 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 6)) = true := by
  decide +kernel
#print axioms coreFlatten618_6
#print axioms coreCheck618_6
end Erdos883Verified
