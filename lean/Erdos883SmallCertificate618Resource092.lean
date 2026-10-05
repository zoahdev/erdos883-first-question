import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_92 :
    (List.ofFn coreChunks618_92).flatten =
      (coreData618.take (coreResources618 92).q).drop 193 := by
  decide +kernel

theorem coreCheck618_92 :
    ∀ c : Fin 1, (coreChunks618_92 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 92)) = true := by
  decide +kernel
#print axioms coreFlatten618_92
#print axioms coreCheck618_92
end Erdos883Verified
