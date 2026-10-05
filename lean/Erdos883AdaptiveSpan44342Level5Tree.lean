import Erdos883AdaptiveSpan44342Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_5 : adaptiveNumericSpans44342_5.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_5 : adaptiveSpanEven44342_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_5 : adaptiveSpanEven44342_5.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_5 : adaptiveSpanEven44342_5.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_5 : adaptiveSpanWhole44342_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_5 : adaptiveSpanWhole44342_5.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_5 : adaptiveSpanWhole44342_5.spans = coreWholeSpans 0 adaptiveNumericSpans44342_5 := by
  decide +kernel
end Erdos883Verified
