import Erdos883AdaptiveSpan44342Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_3 : adaptiveNumericSpans44342_3.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_3 : adaptiveSpanEven44342_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_3 : adaptiveSpanEven44342_3.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_3 : adaptiveSpanEven44342_3.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_3 : adaptiveSpanWhole44342_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_3 : adaptiveSpanWhole44342_3.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_3 : adaptiveSpanWhole44342_3.spans = coreWholeSpans 0 adaptiveNumericSpans44342_3 := by
  decide +kernel
end Erdos883Verified
