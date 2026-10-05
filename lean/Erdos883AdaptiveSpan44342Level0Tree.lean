import Erdos883AdaptiveSpan44342Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_0 : adaptiveNumericSpans44342_0.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_0 : adaptiveSpanEven44342_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_0 : adaptiveSpanEven44342_0.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_0 : adaptiveSpanEven44342_0.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_0 : adaptiveSpanWhole44342_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_0 : adaptiveSpanWhole44342_0.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_0 : adaptiveSpanWhole44342_0.spans = coreWholeSpans 0 adaptiveNumericSpans44342_0 := by
  decide +kernel
end Erdos883Verified
